import JSP000404Research.ThreeFiveExactScaleStrictGapExclusion
import JSP000404Research.ThreeFiveNoTopWeight
import JSP000404Research.NoTopNextLayerFourCentrePacking
import JSP000404Research.ThreeFiveNextSupportTwoRigidity
import Mathlib.Tactic

/-!
# NEW unconditional ORIGINAL n=3, five-centre lower-branch endpoint (delta=0)

The earlier n=3 five-point exceptional profiles remain open for arbitrary
0 ≤ delta < 1/2. At the EXACT integer scale delta=0, however, genuine
AngleCap noncollinearity forces all four normalized projective gaps at
each original centre to be STRICTLY positive.

The strict-gap lemma now excludes quotient total three at every
original centre. Therefore no exponent-two (top) centre can occur.
Moreover every exponent-one (next-layer) centre must have quotient
positive support exactly ONE, since support TWO forces quotient sum
three. Actual four-centre AngleCap transition packing excludes four
distinct exponent-one centres when three have support ONE.

Thus the n=3, five-original-centre dyadic capacity is unconditionally
proved at delta=0: sum 2^exponent ≤ 8. No Hall hypothesis, sorry,
global true-hole payment, synthetic dyadic credit, or reduction of
the original geometric assumptions is involved.

This does NOT exclude the two n=3 five-point motifs when delta>0,
and does NOT close the arbitrary-cardinality root theorem.
-/

namespace JSP000404Research
open scoped BigOperators

/-- Elementary finite extraction: any set of at least four distinct
elements supplies four ORIGINAL distinct elements of that same set. -/
theorem exists_four_distinct_mem_of_card_ge_four
    {V : Type*} [DecidableEq V] (S : Finset V)
    (h4 : 4 ≤ S.card) :
    ∃ s a b c : V, s ∈ S ∧ a ∈ S ∧ b ∈ S ∧ c ∈ S ∧
      s ≠ a ∧ s ≠ b ∧ s ≠ c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  obtain ⟨s, hs⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  have hc1 : 3 ≤ (S.erase s).card := by
    rw [Finset.card_erase_of_mem hs]
    omega
  obtain ⟨a, ha⟩ :=
    Finset.card_pos.mp (show 0 < (S.erase s).card by omega)
  have hc2 : 2 ≤ ((S.erase s).erase a).card := by
    rw [Finset.card_erase_of_mem ha]
    omega
  obtain ⟨b, hb⟩ :=
    Finset.card_pos.mp (show 0 < ((S.erase s).erase a).card by omega)
  have hc3 : 1 ≤ (((S.erase s).erase a).erase b).card := by
    rw [Finset.card_erase_of_mem hb]
    omega
  obtain ⟨c, hc⟩ :=
    Finset.card_pos.mp (show 0 < (((S.erase s).erase a).erase b).card by omega)
  obtain ⟨has, haS⟩ := Finset.mem_erase.mp ha
  obtain ⟨hba, hb1⟩ := Finset.mem_erase.mp hb
  obtain ⟨hbs, hbS⟩ := Finset.mem_erase.mp hb1
  obtain ⟨hcb, hc2⟩ := Finset.mem_erase.mp hc
  obtain ⟨hca, hc1⟩ := Finset.mem_erase.mp hc2
  obtain ⟨hcs, hcS⟩ := Finset.mem_erase.mp hc1
  exact ⟨s,a,b,c,hs,haS,hbS,hcS,
    has.symm,hbs.symm,hcs.symm,hba.symm,hca.symm,hcb.symm⟩

/-- At t=3 exactly, FOUR different original five-point centres
CANNOT all have exponent one. Indeed, every exponent-one centre must
have positive support ONE (not two), and genuine AngleCap transition
packing prohibits three such support-one next-layer centres beside a
fourth next-layer centre. -/
theorem five_centre_exact_three_scale_forbids_four_next
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hcard : Fintype.card V = 5)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hdeltaExact : delta = 0)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b c : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hs : centreExponent (C s) t = 1)
    (ha : centreExponent (C a) t = 1)
    (hb : centreExponent (C b) t = 1)
    (hc : centreExponent (C c) t = 1) : False := by
  have htthree : t = 3 := by rw [hdeltaExact] at ht; linarith
  have hsupportOne (i : V)
      (hi : centreExponent (C i) t = 1) :
      positiveSupport (centreQuotient (C i) t) = 1 := by
    have hclass :=
      actual_deficit_two_support_one_or_two
        (C i) (by decide : 3 ≤ (3 : ℕ))
        hdelta0 hdeltaHalf ht (by simpa using hi)
    rcases hclass with hOne | hTwo
    · exact hOne
    · have hsum := (next_saturated_of_exponent_one_support_two
        (C i) hi hTwo).2.1
      exact False.elim
        (five_centre_exact_three_scale_forbids_quotient_sum_three
          hp hcap hcard htthree hlam i (C i) hsum)
  exact no_three_support_one_among_four_second_layer_centres
    hp hcap (by decide : 3 ≤ (3 : ℕ))
    hdelta0 hdeltaHalf ht hlam
    hsa hsb hsc hab hac hbc
    (C s) (C a) (C b) (C c)
    (by simpa using hs) (by simpa using ha)
    (by simpa using hb) (by simpa using hc)
    (hsupportOne s hs) (hsupportOne a ha) (hsupportOne b hb)

/-- UNCONDITIONAL original geometric dyadic capacity for EXACT t=3
in the genuinely difficult FIVE-centre strip: exponent sum ≤8.
No all-cardinality Hall/all-eight-source credit hypothesis occurs. -/
theorem planar_three_five_exact_three_scale_dyadic_capacity
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hcard : Fintype.card V = 5)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hdeltaExact : delta = 0)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    (∑ i : V, (2 : ℕ) ^ centreExponent (C i) t) ≤ 8 := by
  classical
  let k : V → ℕ := fun i => centreExponent (C i) t
  have htthree : t = 3 := by rw [hdeltaExact] at ht; linarith
  have hdelta1 : delta < 1 := by linarith
  have hexp : ∀ i : V, k i ≤ 1 := by
    intro i
    have hiBound : k i < 3 := by
      exact centreExponent_lt_n (C i) 3 delta t
        (by decide : 1 ≤ (3 : ℕ)) hdelta0 hdelta1 ht
    have hnotTop : k i ≠ 2 := by
      intro htwo
      have hqBound :
          (∑ r, centreQuotient (C i) t r) ≤ 3 :=
        centreQuotient_function_sum_le_n
          (C i) 3 delta t
          (by decide : 1 ≤ (3 : ℕ)) hdelta0 hdelta1 ht
      have hdef : 3 - floorExcess (centreQuotient (C i) t) = 1 := by
        change 3 - k i = 1
        omega
      have hsum := (unit_deficit_structure
        (centreQuotient (C i) t) 3
        (by decide : 2 ≤ (3 : ℕ)) hqBound hdef).2
      exact five_centre_exact_three_scale_forbids_quotient_sum_three
        hp hcap hcard htthree hlam i (C i) hsum
    omega
  by_contra hcapacity
  have hover : 8 < (∑ i : V, (2 : ℕ) ^ k i) := by
    change ¬ (∑ i : V, (2 : ℕ) ^ k i) ≤ 8 at hcapacity
    omega
  have hfour :
      4 ≤ ((Finset.univ : Finset V).filter (fun i => k i = 1)).card :=
    five_centre_no_top_overweight_forces_four_next
      k hcard hexp hover
  let S : Finset V := (Finset.univ : Finset V).filter (fun i => k i = 1)
  obtain ⟨s,a,b,c,hs,ha,hb,hc,hsa,hsb,hsc,hab,hac,hbc⟩ :=
    exists_four_distinct_mem_of_card_ge_four S hfour
  have hs1 : k s = 1 := (Finset.mem_filter.mp hs).2
  have ha1 : k a = 1 := (Finset.mem_filter.mp ha).2
  have hb1 : k b = 1 := (Finset.mem_filter.mp hb).2
  have hc1 : k c = 1 := (Finset.mem_filter.mp hc).2
  exact five_centre_exact_three_scale_forbids_four_next
    hp hcap hcard hdelta0 hdeltaHalf hdeltaExact ht hlam
    hsa hsb hsc hab hac hbc C hs1 ha1 hb1 hc1

#print axioms exists_four_distinct_mem_of_card_ge_four
#print axioms five_centre_exact_three_scale_forbids_four_next
#print axioms planar_three_five_exact_three_scale_dyadic_capacity

end JSP000404Research
