import JSP000404Research.SupportTwoNarrowClusters
import JSP000404Research.ConcreteTransitionInterval
import JSP000404Research.DeficitTwo
import JSP000404Research.PinnedCycleRotation
import Mathlib.Tactic

/-!
# Concrete narrow-cluster certificate from a support-two transition

This packages the pure list theorem SupportTwoNarrowClusters for an actual
centre.  In the extremal support-two regime with transition quotient qe=1,
the unique other positive quotient is n-1 and the remaining two quotient
blocks are identically zero with total scaled width at most delta.
-/

namespace JSP000404Research

theorem supportTwo_qsum_eq_n
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2) :
    (quotientList t C.gaps).sum = n := by
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
      (centreQuotient C t) n hn hQ hdef
  have hsumFn :
      (∑ r, centreQuotient C t r) = n := by
    rcases hstruct with h1 | h2
    · rw [hsupport] at h1
      omega
    · exact h2.2
  rw [← centreQuotient_sum_eq_list_sum C t]
  exact hsumFn

/-- Concrete extremal support-two narrow-cluster certificate. -/
theorem supportTwo_transition_one_has_two_narrow_zero_blocks
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2)
    (cert : HighExponentTransitionIntervalCertificate hp t i C)
    (hqe : cert.qe = 1) :
    ∃ pre post : List ℕ,
    ∃ gpre gpost : List ℝ, ∃ ge : ℝ,
    ∃ leftQ rightQ : List ℕ,
    ∃ leftG rightG : List ℝ, ∃ gh : ℝ,
      quotientList t C.gaps = pre ++ 1 :: post ∧
      C.gaps = gpre ++ ge :: gpost ∧
      pre.length = gpre.length ∧
      post.length = gpost.length ∧
      post ++ pre = leftQ ++ (n - 1) :: rightQ ∧
      gpost ++ gpre = leftG ++ gh :: rightG ∧
      leftQ.length = leftG.length ∧
      rightQ.length = rightG.length ∧
      (∀ x ∈ leftQ, x = 0) ∧
      (∀ x ∈ rightQ, x = 0) ∧
      (((n - 1 : ℕ) : ℝ) ≤ t * gh) ∧
      t * (leftG.sum + rightG.sum) ≤ delta := by
  have hdelta1 : delta < 1 := by linarith
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hqmem :
      1 ∈ quotientList t C.gaps := by
    simpa [hqe] using cert.qe_mem
  obtain ⟨pre,post,hsplit⟩ :=
    exists_append_cons_of_mem hqmem
  have hsupportList :
      listPositiveCount (quotientList t C.gaps) = 2 := by
    rw [← centreQuotient_ofFn]
    rw [listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupport
  have hqsum :=
    supportTwo_qsum_eq_n
      hn hdelta0 hdelta1 ht C hexp hsupport
  have halign :=
    centreQuotient_aligned C htpos.le
  obtain ⟨gpre,gpost,ge,
      leftQ,rightQ,leftG,rightG,gh,
      hgaps,hpreLen,hpostLen,
      hhiddenQ,hhiddenG,
      hleftLen,hrightLen,
      hleftZero,hrightZero,
      hhiddenAlign,hzeroWidth⟩ :=
    exists_two_narrow_zero_blocks
      (quotientList t C.gaps) C.gaps
      pre post hn ht htpos
      hsplit hsupportList hqsum C.gaps_sum halign
      (mixed_support_two_has_hidden_n_sub_one
        C cert hn hdelta0 hdeltaHalf ht
        hexp hsupport hqe)
  exact ⟨pre,post,gpre,gpost,ge,
    leftQ,rightQ,leftG,rightG,gh,
    hsplit,hgaps,hpreLen,hpostLen,
    hhiddenQ,hhiddenG,
    hleftLen,hrightLen,
    hleftZero,hrightZero,
    hhiddenAlign,hzeroWidth⟩

#print axioms supportTwo_qsum_eq_n
#print axioms supportTwo_transition_one_has_two_narrow_zero_blocks

end JSP000404Research
