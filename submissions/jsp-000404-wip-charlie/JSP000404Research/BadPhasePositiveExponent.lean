import JSP000404Research.BoundaryFailureStructure
import JSP000404Research.WeightedBadPhaseCapacity
import Mathlib.Tactic

/-!
# Genuine one-exception budget failures have positive Sendov exponent

BoundaryFailureStructure proves that a strict local budget failure forces the
exceptional geometric quotient to satisfy q(e) >= 2.  Since floorExcess(q) is

  sum_i (q(i)-1),

the centre exponent is therefore at least one.

Consequently, in the one-exception phase model, every bad centre has dyadic
weight at least two.  The weighted relaxation B <= 1 from
WeightedBadPhaseCapacity cannot tolerate a genuine bad centre: under this
geometry B <= 1 is equivalent to having no bad centre at all.

This is a useful hard-stop lemma for the global search.  It prevents treating
an exponent-zero centre as the one allowed bad vertex.
-/

namespace JSP000404Research

open scoped BigOperators

theorem floorExcess_one_le_of_two_le_coordinate
    {I : Type*} [Fintype I]
    (q : I → ℕ) (e : I)
    (he : 2 ≤ q e) :
    1 ≤ floorExcess q := by
  unfold floorExcess
  have hsingle :
      q e - 1 ≤ ∑ i : I, (q i - 1) := by
    exact Finset.single_le_sum
      (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ e)
  omega

theorem floorExcess_one_le_of_budget_failure
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (e : I) (n : ℕ)
    (hsum : (∑ i, b i) = n)
    (hregular : ∀ i, i ≠ e → q i ≤ b i)
    (hexception : q e ≤ b e + 1)
    (hbad : n - floorExcess q < positiveSupport b) :
    1 ≤ floorExcess q := by
  have hqe :
      2 ≤ q e :=
    exceptional_quotient_two_le_of_budget_failure
      q b e n hsum hregular hexception hbad
  exact floorExcess_one_le_of_two_le_coordinate q e hqe

/-- If every over-budget vertex has positive exponent, then one bad vertex
already contributes at least two units to the weighted bad mass. -/
theorem two_le_badPhaseWeight_of_exists_bad_positive
    {V : Type*} [Fintype V]
    (n : ℕ)
    (exponent active : V → ℕ)
    (hpos :
      ∀ v, n - exponent v < active v → 1 ≤ exponent v)
    (hex : ∃ v, n - exponent v < active v) :
    2 ≤ badPhaseWeight n exponent active := by
  classical
  obtain ⟨v, hv⟩ := hex
  have hvpow : 2 ≤ 2 ^ exponent v := by
    have hmono :=
      Nat.pow_le_pow_right
        (by norm_num : 0 < 2)
        (hpos v hv)
    norm_num at hmono ⊢
    exact hmono
  unfold badPhaseWeight
  have hsingle :
      (if n - exponent v < active v then 2 ^ exponent v else 0)
        ≤
      ∑ w : V,
        (if n - exponent w < active w
         then 2 ^ exponent w else 0) := by
    exact Finset.single_le_sum
      (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ v)
  simp [hv] at hsingle
  exact hvpow.trans hsingle

/-- Hence bad weight at most one forces every local budget to be good whenever
genuine bad vertices necessarily have positive exponent. -/
theorem no_bad_of_badPhaseWeight_le_one_of_bad_positive
    {V : Type*} [Fintype V]
    (n : ℕ)
    (exponent active : V → ℕ)
    (hpos :
      ∀ v, n - exponent v < active v → 1 ≤ exponent v)
    (hbadWeight :
      badPhaseWeight n exponent active ≤ 1) :
    ∀ v, active v ≤ n - exponent v := by
  intro v
  by_contra hv
  have hvbad :
      n - exponent v < active v := by omega
  have htwo :=
    two_le_badPhaseWeight_of_exists_bad_positive
      n exponent active hpos ⟨v, hvbad⟩
  omega

#print axioms floorExcess_one_le_of_two_le_coordinate
#print axioms floorExcess_one_le_of_budget_failure
#print axioms two_le_badPhaseWeight_of_exists_bad_positive
#print axioms no_bad_of_badPhaseWeight_le_one_of_bad_positive

end JSP000404Research
