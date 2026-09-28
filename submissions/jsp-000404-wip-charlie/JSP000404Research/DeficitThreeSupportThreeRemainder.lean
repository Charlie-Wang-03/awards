import JSP000404Research.FullMassPointwiseRemainder
import JSP000404Research.SixPointExactWitnessTerminal
import Mathlib.Tactic

/-!
# Exact fractional remainder mass in the deficit-three/support-three branch

For a concrete centre with

  exponent = n-3,
  positive quotient support = 3,

the deficit-three zero-carry identity forces the total quotient mass to be
exactly n.  Since the normalized projective gaps sum to one and
t = n + delta, the aligned floor remainders have exact total mass delta:

  sum_r (t*g_r - q_r) = delta.

This is stronger than the existing pointwise upper bounds and is the natural
real-valued bookkeeping invariant for the final support-three terminal.
-/

namespace JSP000404Research

theorem centre_remainderMass_eq_delta_of_deficit_three_support_three
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hexp : centreExponent C t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient C t) = 3) :
    listRemainderMass t
        (quotientList t C.gaps) C.gaps
      = delta := by
  have hdelta1 : delta < 1 := by linarith
  have hQ :=
    centreQuotient_function_sum_le_n
      C n delta t (by omega : 1 ≤ n)
      hdelta0 hdelta1 ht
  have hell :
      n - floorExcess (centreQuotient C t) = 3 := by
    change n - centreExponent C t = 3
    rw [hexp]
    omega
  have hstruct :=
    deficit_three_structure
      (centreQuotient C t) n hn hQ hell
  have hsumFn :
      (∑ r, centreQuotient C t r) = n := by
    rcases hstruct with h1 | h2 | h3
    · rw [hsupport] at h1
      omega
    · rw [hsupport] at h2
      omega
    · exact h3.2
  have hsumList :
      (quotientList t C.gaps).sum = n := by
    rw [← centreQuotient_sum_eq_list_sum C t]
    exact hsumFn
  have hlen :
      (quotientList t C.gaps).length = C.gaps.length :=
    quotientList_length t C.gaps
  rw [listRemainderMass_eq t
      (quotientList t C.gaps) C.gaps hlen,
    C.gaps_sum, hsumList, ht]
  norm_num

/-- Every individual aligned gap remainder is nonnegative and bounded by
delta in the support-three deficit-three branch. -/
theorem centre_gap_remainder_between_zero_delta_of_deficit_three_support_three
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hexp : centreExponent C t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient C t) = 3)
    (r : Fin C.gaps.length) :
    0 ≤
        t * C.gaps.get r -
          (centreQuotient C t r : ℝ)
      ∧
    t * C.gaps.get r -
          (centreQuotient C t r : ℝ)
      ≤ delta := by
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have halign :=
    centreQuotient_aligned C htpos.le
  have hget :
      (centreQuotient C t r : ℝ) ≤
        t * C.gaps.get r := by
    exact List.Forall₂.get halign
      (Fin.cast (quotientList_length t C.gaps).symm r)
      r rfl
  have htotal :=
    centre_remainderMass_eq_delta_of_deficit_three_support_three
      C hn hdelta0 hdeltaHalf ht hexp hsupport
  have hdisplay :
      t * C.gaps.get r -
          (centreQuotient C t r : ℝ)
        ≤
      listRemainderMass t
        (quotientList t C.gaps) C.gaps := by
    -- Use the aligned-list total remainder bound by splitting at r.
    let qpre := (quotientList t C.gaps).take r.val
    let qpost := (quotientList t C.gaps).drop (r.val + 1)
    let gpre := C.gaps.take r.val
    let gpost := C.gaps.drop (r.val + 1)
    have hqdecomp :
        quotientList t C.gaps =
          qpre ++ centreQuotient C t r :: qpost := by
      dsimp [qpre, qpost]
      have hrq :
          r.val < (quotientList t C.gaps).length := by
        rw [quotientList_length]
        exact r.isLt
      simpa [centreQuotient] using
        (List.take_append_getElem_drop
          (quotientList t C.gaps) r.val hrq)
    have hgdecomp :
        C.gaps =
          gpre ++ C.gaps.get r :: gpost := by
      dsimp [gpre, gpost]
      simpa using
        (List.take_append_getElem_drop
          C.gaps r.val r.isLt)
    have hpreLen : qpre.length = gpre.length := by
      dsimp [qpre, gpre]
      rw [List.length_take, List.length_take,
        quotientList_length]
    have halign' :
        QuotientGapAligned t
          (qpre ++ centreQuotient C t r :: qpost)
          (gpre ++ C.gaps.get r :: gpost) := by
      simpa [hqdecomp, hgdecomp] using halign
    have h :=
      displayed_remainder_le_listRemainderMass
        qpre qpost gpre gpost
        (centreQuotient C t r)
        (C.gaps.get r) hpreLen halign'
    simpa [hqdecomp, hgdecomp] using h
  rw [htotal] at hdisplay
  exact ⟨by linarith, hdisplay⟩

#print axioms centre_remainderMass_eq_delta_of_deficit_three_support_three
#print axioms centre_gap_remainder_between_zero_delta_of_deficit_three_support_three

end JSP000404Research
