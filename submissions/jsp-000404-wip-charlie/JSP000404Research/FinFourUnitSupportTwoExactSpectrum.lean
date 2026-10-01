import JSP000404Research.FinFourCentreCycle
import JSP000404Research.SupportTwoTransitionClusterBridge
import JSP000404Research.SecondLayerUnitTransitionBandRigidity
import Mathlib.Tactic

/-!
# Exact three-gap quotient spectrum at a Fin-4 unit-transition support-two centre

At a four-point centre there are exactly three cyclic quotient entries.
In the second-layer support-two unit-transition regime:
* support is exactly two;
* total quotient sum is n;
* one distinguished transition quotient is 1;
* every quotient belongs to {0,1,n-1}.

Therefore the three quotient entries are exactly a permutation of
[0,1,n-1].
-/

namespace JSP000404Research

theorem fin4_unitSupportTwo_quotient_multiset_eq
    {p : Fin 4 → Plane}
    {hp : Function.Injective p}
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : Fin 4)
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2)
    (cert : HighExponentTransitionIntervalCertificate hp t i C)
    (hqe : cert.qe = 1) :
    (quotientList t C.gaps).toFinset = {0,1,n-1} ∧
    (quotientList t C.gaps).count 0 = 1 ∧
    (quotientList t C.gaps).count 1 = 1 ∧
    (quotientList t C.gaps).count (n-1) = 1 := by
  classical
  have hlen :
      (quotientList t C.gaps).length = 3 := by
    rw [quotientList_length]
    exact centreProjectiveCycle_gaps_length_fin4 i C

  have hspec :
      ∀ q ∈ quotientList t C.gaps,
        q = 0 ∨ q = 1 ∨ q = n - 1 :=
    supportTwo_transition_one_quotient_spectrum
      (hp := hp) hcap hn3 hdelta0 hdeltaHalf ht hlam
      C hexp hsupport cert hqe

  have hq1mem :
      1 ∈ quotientList t C.gaps := by
    simpa [hqe] using cert.qe_mem

  have hsum :
      (quotientList t C.gaps).sum = n :=
    supportTwo_qsum_eq_n
      hn3 hdelta0 (by linarith : delta < 1) ht
      C hexp hsupport

  have hpos :
      listPositiveCount (quotientList t C.gaps) = 2 := by
    rw [← centreQuotient_ofFn C t]
    rw [listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupport

  have hn1pos : 1 < n - 1 := by omega

  -- With length three, exactly two positive entries, one equal to 1,
  -- and total sum n, the remaining positive entry is n-1 and the
  -- remaining entry is zero.
  obtain ⟨a,b,c,hlist⟩ :
      ∃ a b c : ℕ, quotientList t C.gaps = [a,b,c] := by
    exact List.length_eq_three.mp hlen
  rw [hlist] at hspec hq1mem hsum hpos ⊢
  simp only [List.mem_cons, List.mem_singleton] at hq1mem
  simp only [List.sum_cons, List.sum_nil, add_zero] at hsum
  simp [listPositiveCount] at hpos
  have ha := hspec a (by simp)
  have hb := hspec b (by simp)
  have hc := hspec c (by simp)
  rcases ha with rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;>
    simp_all [listPositiveCount] <;> omega

#print axioms fin4_unitSupportTwo_quotient_multiset_eq

end JSP000404Research
