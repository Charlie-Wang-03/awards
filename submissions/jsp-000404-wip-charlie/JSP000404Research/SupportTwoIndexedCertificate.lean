import JSP000404Research.FourCentreTransitionCases
import JSP000404Research.GapRemainder
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Indexed certificate for the extremal support-two split 1 + (n-1)

For a deficit-two/support-two centre with distinguished transition quotient one,
the centre quotient function has exactly two positive coordinates.

The transition certificate supplies one coordinate with value 1, while the
hidden-quotient theorem supplies another coordinate with value n-1.  Since
n>=3 these coordinates are distinct, and support=2 forces every other quotient
coordinate to be zero.

Moreover the quotient sum is n, so the ordinary remainder budget gives a
global bound on all zero-quotient gaps:

  zeroGapMass <= delta/t.

This packages the hardest support-two profile as two indexed positive gaps plus
a uniformly tiny zero-gap remainder.
-/

namespace JSP000404Research

open scoped BigOperators

def positiveIndexSet
    {I : Type*} [Fintype I]
    (q : I → ℕ) : Finset I :=
  (Finset.univ : Finset I).filter fun i => q i ≠ 0

theorem positiveIndexSet_card
    {I : Type*} [Fintype I]
    (q : I → ℕ) :
    (positiveIndexSet q).card = positiveSupport q := by
  classical
  unfold positiveIndexSet positiveSupport
  simp [Finset.card_eq_sum_ones]

structure SupportTwoUnitTransitionIndexedCertificate
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t delta : ℝ) (n : ℕ) where
  transitionIndex : Fin C.gaps.length
  hiddenIndex : Fin C.gaps.length
  indices_ne : transitionIndex ≠ hiddenIndex
  transition_eq_one :
    centreQuotient C t transitionIndex = 1
  hidden_eq_n_sub_one :
    centreQuotient C t hiddenIndex = n - 1
  other_eq_zero :
    ∀ r,
      r ≠ transitionIndex →
      r ≠ hiddenIndex →
      centreQuotient C t r = 0
  quotient_sum :
    (∑ r, centreQuotient C t r) = n
  zero_gap_mass_le :
    zeroGapMass
      (fun r => C.gaps.get r)
      (centreQuotient C t) ≤ delta / t

theorem exists_supportTwoUnitTransitionIndexedCertificate
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
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
    Nonempty
      (SupportTwoUnitTransitionIndexedCertificate
        C t delta n) := by
  have hdelta1 : delta < 1 := by linarith
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hsumBound :=
    centreQuotient_function_sum_le_n
      C n delta t (by omega : 1 ≤ n)
      hdelta0 hdelta1 ht
  have hdef :
      n - floorExcess (centreQuotient C t) = 2 := by
    rw [← show centreExponent C t =
      floorExcess (centreQuotient C t) by rfl, hexp]
    omega
  have hstruct :=
    deficit_two_structure
      (centreQuotient C t) n hn hsumBound hdef
  have hsum :
      (∑ r, centreQuotient C t r) = n := by
    rcases hstruct with h1 | h2
    · rw [hsupport] at h1
      omega
    · exact h2.2

  have htransMem :
      1 ∈ List.ofFn (centreQuotient C t) := by
    rw [centreQuotient_ofFn C t]
    rw [← hqe]
    exact cert.qe_mem
  rw [List.mem_ofFn'] at htransMem
  obtain ⟨rt, hrt⟩ := htransMem

  have hhiddenList :
      n - 1 ∈ quotientList t C.gaps :=
    mixed_support_two_has_hidden_n_sub_one
      C cert hn hdelta0 hdeltaHalf ht
      hexp hsupport hqe
  have hhiddenMem :
      n - 1 ∈ List.ofFn (centreQuotient C t) := by
    rw [centreQuotient_ofFn C t]
    exact hhiddenList
  rw [List.mem_ofFn'] at hhiddenMem
  obtain ⟨rh, hrh⟩ := hhiddenMem

  have hrtVal :
      centreQuotient C t rt = 1 := hrt.symm
  have hrhVal :
      centreQuotient C t rh = n - 1 := hrh.symm
  have hrne : rt ≠ rh := by
    intro h
    subst rh
    rw [hrtVal] at hrhVal
    omega

  let S :=
    positiveIndexSet (centreQuotient C t)
  have hcardS : S.card = 2 := by
    dsimp [S]
    rw [positiveIndexSet_card, hsupport]
  have hrtS : rt ∈ S := by
    simp [S, positiveIndexSet, hrtVal]
  have hrhS : rh ∈ S := by
    have hnsub : n - 1 ≠ 0 := by omega
    simp [S, positiveIndexSet, hrhVal, hnsub]
  have hpairSub : ({rt, rh} : Finset _) ⊆ S := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact hrtS
    · exact hrhS
  have hpairCard :
      ({rt, rh} : Finset _).card = 2 := by
    simp [hrne]
  have hSeq : S = {rt, rh} := by
    apply Finset.eq_of_subset_of_card_le hpairSub
    rw [hpairCard, hcardS]

  have hother :
      ∀ r,
        r ≠ rt →
        r ≠ rh →
        centreQuotient C t r = 0 := by
    intro r hrtNe hrhNe
    by_contra hr0
    have hrS : r ∈ S := by
      simp [S, positiveIndexSet, hr0]
    rw [hSeq] at hrS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hrS
    exact hrS.elim hrtNe hrhNe

  let gap : Fin C.gaps.length → ℝ :=
    fun r => C.gaps.get r
  have hgapSum :
      (∑ r, gap r) = 1 := by
    have h := C.gaps_sum
    simpa [gap, ← List.sum_ofFn] using h
  have hgap0 :
      ∀ r, 0 ≤ gap r := by
    intro r
    exact C.gaps_nonneg (gap r) (by
      dsimp [gap]
      exact C.gaps.get_mem r)
  have hfloor :
      ∀ r,
        ((centreQuotient C t r : ℕ) : ℝ) ≤
          t * gap r := by
    intro r
    unfold centreQuotient
    exact Nat.floor_le (mul_nonneg htpos.le (hgap0 r))
  have hzero :=
    zeroGapMass_le_delta_div
      gap (centreQuotient C t)
      n delta t ht htpos
      hgapSum hsum hfloor

  exact ⟨{
    transitionIndex := rt
    hiddenIndex := rh
    indices_ne := hrne
    transition_eq_one := hrtVal
    hidden_eq_n_sub_one := hrhVal
    other_eq_zero := hother
    quotient_sum := hsum
    zero_gap_mass_le := by simpa [gap] using hzero
  }⟩

#print axioms positiveIndexSet_card
#print axioms exists_supportTwoUnitTransitionIndexedCertificate

end JSP000404Research
