import JSP000404Research.PlanarLowerTwoAllCentresExposed
import JSP000404Research.ExposedSupportIntervalGeneral
import JSP000404Research.SupportIntervalCertificate
import JSP000404Research.PlanarKnownSmallCentreCapacity
import JSP000404Research.PlanarLowerTwoFourUnconditionalCapacity
import Mathlib.Tactic

/-!
# Fully close the entire genuine planar n=2 lower branch

From actual AngleCap and the quotient mass at t=2+delta, every genuine
centre is strictly exposed. The GENERAL (arbitrary-cardinality) exposed
support-interval lemma constructs at each centre a certificate with
turn length at least lambda. All distinct centres' support arcs are
pairwise disjoint on the circle and their total turn length is <=2*pi.

Therefore |V|*lambda<=2*pi; since lambda=pi/(2+delta) and delta<1/2,
|V|<5, i.e. |V|<=4. The previously kernel-checked two-, three- and
unconditional four-centre capacity lemmas then give the sharp sum bound.

No global Boolean payment, extra sharp exclusion or admitted axiom.
-/

namespace JSP000404Research

theorem lower_two_original_card_le_four
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (2 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    Fintype.card V ≤ 4 := by
  classical
  have htpos : 0 < t := by rw [ht]; linarith
  have htone : (1 : ℝ) ≤ t := by rw [ht]; linarith
  have hcert (i : V) :
      ∃ S : SupportIntervalCertificate (p := p) i,
        lam ≤ S.turnLength :=
    exists_supportIntervalCertificate_of_strictlyExposed
      hp hcap htpos htone hlam (C i)
      (lower_two_all_centres_strictlyExposed
        hp hcap hdelta0 hdeltaHalf ht hlam C i)
  let cert : ∀ i : V, SupportIntervalCertificate (p := p) i :=
    fun i => Classical.choose (hcert i)
  have hbound (i : V) : lam ≤ (cert i).turnLength :=
    Classical.choose_spec (hcert i)
  have hsum :
      (Fintype.card V : ℝ) * lam ≤ 2 * Real.pi := by
    calc
      (Fintype.card V : ℝ) * lam = ∑ _i : V, lam := by simp
      _ ≤ ∑ i : V, (cert i).turnLength :=
        Finset.sum_le_sum (by intro i _; exact hbound i)
      _ ≤ 2 * Real.pi := by
        simpa only using
          (SupportIntervalCertificate.turnLength_sum_le_two_pi
            (fun i : V => i) (fun _ _ h => h) cert)
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hpi : Real.pi = t * lam := by
    rw [hlam]
    field_simp [ne_of_gt htpos]
  have hscaled : (Fintype.card V : ℝ) * lam ≤ (2 * t) * lam := by
    calc
      (Fintype.card V : ℝ) * lam ≤ 2 * Real.pi := hsum
      _ = (2 * t) * lam := by rw [hpi]; ring
  have hcount : (Fintype.card V : ℝ) ≤ 2 * t :=
    (mul_le_mul_right hlampos).mp hscaled
  have hreal : (Fintype.card V : ℝ) < 5 := by
    rw [ht] at hcount
    linarith
  have hnat : Fintype.card V < 5 := by exact_mod_cast hreal
  omega

namespace ProjectionOrdered

theorem planar_lower_branch_n_two_all_centre_dyadic_capacity
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (2 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (cycles :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
    (∑ i : ProjectionOrdered V,
      (2 : ℕ) ^ centreExponent (cycles i) t) ≤ 2 ^ 2 := by
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have hcapRe : AngleCap (reindexedPoint p) lam :=
    angleCap_reindexedPoint hp hcap
  have hcard : Fintype.card (ProjectionOrdered V) ≤ 4 :=
    lower_two_original_card_le_four
      (reindexedPoint_injective hp) hcapRe
      hdelta0 hdeltaHalf ht hlam cycles
  by_cases hsmall : Fintype.card (ProjectionOrdered V) ≤ 2
  · exact planar_lower_branch_known_small_centre_dyadic_capacity
      hp hcap (by omega : 1 ≤ 2)
      hdelta0 hdeltaHalf (by simpa only [Nat.cast_ofNat] using ht)
      hlam cycles (Or.inl hsmall)
  · by_cases hthree : Fintype.card (ProjectionOrdered V) = 3
    · exact planar_lower_branch_known_small_centre_dyadic_capacity
        hp hcap (by omega : 1 ≤ 2)
        hdelta0 hdeltaHalf (by simpa only [Nat.cast_ofNat] using ht)
        hlam cycles (Or.inr (Or.inl ⟨hthree, by omega⟩))
    · have hfour : Fintype.card (ProjectionOrdered V) = 4 := by omega
      exact lower_two_four_original_centre_dyadic_capacity
        (reindexedPoint_injective hp) hcapRe hfour
        hdelta0 hdeltaHalf ht hlam cycles

#print axioms planar_lower_branch_n_two_all_centre_dyadic_capacity

end ProjectionOrdered

#print axioms lower_two_original_card_le_four

end JSP000404Research
