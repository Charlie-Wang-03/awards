import JSP000404Research.PlanarThreeJointWideAngleNarrowGap
import JSP000404Research.ThreeFiveSaturatedUnitQuotients
import Mathlib.Tactic

/-!
# Many genuine original centres jointly carry full n=3 geometric rigidity

The independently established >=N-6 counts of genuine original
strict >120-degree angle apices and high-support centres yield
>=N-12 original centres in their intersection. This module proves
that EVERY such centre, not just one, has a full source-native
profile certificate:

* actual exponent ZERO, exact positive support THREE,
  all real quotient entries at most ONE, and THREE unit quotients;
* an actual original >120-degree angle at THAT vertex with the
  exact reciprocal-strip inequality;
* an actual positive zero-quotient projective gap at THAT vertex,
  with its N-dependent narrow-gap inequality.

No cross-vertex credit, Boolean exterior-hole claim, or re-use of
dyadic surplus is asserted. Nine-point extremal geometry and the
original full eight-source global payment remain open.
-/

namespace JSP000404Research

/-- Genuine, typed and classically decidable ORIGINAL centre carriers.
The conditions describe simultaneously available geometric facts
at each ORIGINAL centre, not available Boolean payment credits. -/
noncomputable def originalThreeFullCertifiedCentres
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (t delta : ℝ)
    (C : ∀ i : V, CentreProjectiveCycle hp i) : Finset V := by
  classical
  exact (Finset.univ : Finset V).filter (fun i =>
    centreExponent (C i) t = 0 ∧
    positiveSupport (centreQuotient (C i) t) = 3 ∧
    (∀ r, centreQuotient (C i) t r ≤ 1) ∧
    unitSupport (centreQuotient (C i) t) = 3 ∧
    (∃ a c : V,
      a ≠ i ∧ a ≠ c ∧ i ≠ c ∧
      Real.pi - Real.pi / 3 <
        EuclideanGeometry.angle (p a) (p i) (p c) ∧
      Real.pi /
        (Real.pi - EuclideanGeometry.angle (p a) (p i) (p c)) -
          3 ≤ delta) ∧
    (∃ r : Fin (C i).gaps.length,
      centreQuotient (C i) t r = 0 ∧
      0 < (C i).gaps.get r ∧
      ((Fintype.card V - 4 : ℕ) : ℝ) *
        (t * (C i).gaps.get r) ≤ delta))

/-- The COMPLETE original full-certificate centre family contains
the genuine wide-angle/high-support intersection whenever N>=7. -/
theorem original_three_wide_high_support_subset_fully_certified
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hcard : 7 ≤ Fintype.card V)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    originalThreeWideHighSupportCentres t C ⊆
      originalThreeFullCertifiedCentres hp t delta C := by
  classical
  intro i hi
  have hpair :
      OriginalWideAngleApex p i ∧
      3 ≤ positiveSupport (centreQuotient (C i) t) := by
    simpa [originalThreeWideHighSupportCentres] using hi
  obtain ⟨hk, hsup, _hsum⟩ :=
    three_scale_high_support_exact_rigidity
      (C i) hdelta0 hdeltaHalf ht hpair.2
  obtain ⟨hunit, hunitCount⟩ :=
    three_scale_support_three_all_unit_quotients
      (C i) hdelta0 hdeltaHalf ht hpair.2
  obtain ⟨a, c, hai, hac, hic, hwide⟩ := hpair.1
  have hcapAngle :
      EuclideanGeometry.angle (p a) (p i) (p c) ≤
        Real.pi - Real.pi / t := by
    simpa [hlam] using (hcap a i c hai hac hic)
  have hpaid :=
    three_scale_exact_angle_threshold hdelta0 ht hcapAngle
  have hgap :=
    planar_three_every_high_support_centre_has_narrow_gap
      hp hcap hcard hdelta0 hdeltaHalf ht hlam C i hpair.2
  have hFull :
      centreExponent (C i) t = 0 ∧
      positiveSupport (centreQuotient (C i) t) = 3 ∧
      (∀ r, centreQuotient (C i) t r ≤ 1) ∧
      unitSupport (centreQuotient (C i) t) = 3 ∧
      (∃ a c : V,
        a ≠ i ∧ a ≠ c ∧ i ≠ c ∧
        Real.pi - Real.pi / 3 <
          EuclideanGeometry.angle (p a) (p i) (p c) ∧
        Real.pi /
          (Real.pi - EuclideanGeometry.angle (p a) (p i) (p c)) -
            3 ≤ delta) ∧
      (∃ r : Fin (C i).gaps.length,
        centreQuotient (C i) t r = 0 ∧
        0 < (C i).gaps.get r ∧
        ((Fintype.card V - 4 : ℕ) : ℝ) *
          (t * (C i).gaps.get r) ≤ delta) :=
    ⟨hk, hsup, hunit, hunitCount,
     ⟨a, c, hai, hac, hic, hwide, hpaid⟩, hgap⟩
  simpa [originalThreeFullCertifiedCentres] using hFull

/-- The full source-native certificate exists simultaneously at
at least N-12 DIFFERENT original centres, not merely one centre
when N>=13. The count is unconditional on any nine-point lemma. -/
theorem planar_three_full_certified_centres_card_add_twelve
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hcard : 7 ≤ Fintype.card V)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    Fintype.card V ≤
      (originalThreeFullCertifiedCentres hp t delta C).card + 12 := by
  have hsource :=
    planar_three_wide_angle_and_high_support_card_add_twelve
      hp hcap hdelta0 hdeltaHalf ht hlam C
  have hsubset :=
    original_three_wide_high_support_subset_fully_certified
      hp hcap hcard hdelta0 hdeltaHalf ht hlam C
  have hcardmon := Finset.card_le_card hsubset
  omega

#print axioms original_three_wide_high_support_subset_fully_certified
#print axioms planar_three_full_certified_centres_card_add_twelve

end JSP000404Research
