import JSP000404Research.SeparatedSupportTwoResidualBudget
import JSP000404Research.ZeroAngleMassStrictPos
import Mathlib.Tactic

/-!
# Six-centre strict exclusion at the one-third threshold

At exactly six original centres, a support-two quotient cycle with both
top-adjacent endpoint quotients zero has three middle quotient slots,
exactly two of them positive. The remaining zero slot carries a strictly
positive actual angle under AngleCap. The one-third zero-mass bound then
gives a contradiction. This is an actual geometric boundary exclusion,
not the six-source global Boolean-hole payment.
-/

namespace JSP000404Research

theorem listPositiveCount_eq_length_of_all_ne_zero
    (qs : List ℕ) (h : ∀ q ∈ qs, q ≠ 0) :
    listPositiveCount qs = qs.length := by
  induction qs with
  | nil => simp [listPositiveCount]
  | cons q qs ih =>
      have hq : q ≠ 0 := h q (by simp)
      have hrest : ∀ x ∈ qs, x ≠ 0 := by
        intro x hx
        exact h x (by simp [hx])
      simp [listPositiveCount, hq, ih hrest]
      omega

theorem middle_zero_of_three_slots_and_two_positive
    (qFirst qLast : ℕ) (qmid : List ℕ)
    (hmid3 : qmid.length = 3)
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

/-- With six actual original centres and delta=1/3, a separated
support-two deficit-three centre cannot have *both* sharp-top adjacent
quotient endpoints equal to zero. -/
theorem separated_support_two_six_centres_no_double_zero_at_third
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (Cfam : ∀ v : V, CentreProjectiveCycle hp v)
    (hSix : Fintype.card V = 6)
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
  have hOtherFive : Fintype.card (OtherVertex i) = 5 := by
    change Fintype.card {v : V // v ≠ i} = 5
    rw [Fintype.card_subtype_compl (fun v : V => v = i)]
    simp [hSix]
  have hRayFive : (Cfam i).rays.length = 5 := by
    have hc := List.toFinset_card_of_nodup (Cfam i).nodup
    have hcardSet :
        (Cfam i).rays.toFinset.card = 5 := by
      have hcompleteCard :=
        congrArg Finset.card (Cfam i).complete
      simpa [hSix] using hcompleteCard
    omega
  have hQuotFive : (quotientList t (Cfam i).gaps).length = 5 := by
    rw [quotientList_length, (Cfam i).gaps_length]
    exact hRayFive
  have hRotFive : ((quotientList t (Cfam i).gaps).rotate k).length = 5 := by
    simpa using hQuotFive
  rw [hquot] at hRotFive
  simp only [List.length_cons, List.length_append, List.length_singleton,
    List.length_nil] at hRotFive
  have hmid3 : qmid.length = 3 := by omega
  have hmidPosCount :
      listPositiveCount (qFirst :: qmid ++ [qLast]) = 2 := by
    rw [← hquot, listPositiveCount_rotate]
    rw [← centreQuotient_ofFn (Cfam i) t,
        listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupport
  have hzero : 0 ∈ qmid :=
    middle_zero_of_three_slots_and_two_positive
      qFirst qLast qmid hmid3 hmidPosCount hends
  have hRotRaysFive : ((Cfam i).rays.rotate k).length = 5 := by
    simpa using hRayFive
  rw [hrays] at hRotRaysFive
  simp only [List.length_cons] at hRotRaysFive
  have hrest3 : rest.length = 3 := by omega
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

#print axioms middle_zero_of_three_slots_and_two_positive
#print axioms separated_support_two_six_centres_no_double_zero_at_third

end JSP000404Research
