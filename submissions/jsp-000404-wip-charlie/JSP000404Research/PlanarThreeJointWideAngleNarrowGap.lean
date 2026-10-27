import JSP000404Research.PlanarSevenExactAngleThreshold
import JSP000404Research.PlanarThreeManyQuantitativeGapMultiplicity
import Mathlib.Tactic

/-!
# An original centre with BOTH an exact wide-angle debit and a narrow zero gap

Two unconditional genuine-plane n=3 counting theorems prove that:
* at least N-6 distinct original vertices are apexes of a >120-degree
  original triangle;
* at least N-6 distinct original vertices have a genuinely positive
  zero-quotient projective gap whose scaled length is <=delta/(N-4).

For N>=13 these two subsets MUST intersect at an original vertex,
by cardinality inclusion-exclusion.  At this SAME centre we get both
the exact angle payment

   pi/(pi-theta) - 3 <= delta

and the narrow-zero-gap inequality

   (N-4)*t*gap <= delta.

This does NOT assert that the two credits may be added or re-used to
pay global Boolean debt. In particular it does not rule out all
N>=13 cases, prove the 9-point 5*pi/7 threshold, or discharge the
original eight-source nonreuse WIP sorry.
-/

namespace JSP000404Research
open scoped BigOperators

/-- For N>=13 original centres, angle-excess and narrow-gap
certificates necessarily occur at the SAME original centre.
All geometric premises are the actual original AngleCap contract. -/
theorem planar_three_thirteen_centres_joint_exact_angle_narrow_gap
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hcard : 13 ≤ Fintype.card V)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    ∃ i : V,
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
          (t * (C i).gaps.get r) ≤ delta) := by
  classical
  let G : Finset V := originalWideAngleApexFinset p
  let H : Finset V :=
    (Finset.univ : Finset V).filter
      (fun i : V =>
        ∃ r : Fin (C i).gaps.length,
          centreQuotient (C i) t r = 0 ∧
          0 < (C i).gaps.get r ∧
          ((Fintype.card V - 4 : ℕ) : ℝ) *
            (t * (C i).gaps.get r) ≤ delta)
  have hG : Fintype.card V ≤ G.card + 6 :=
    original_many_wide_angle_apices p hp
  have hH : Fintype.card V ≤ H.card + 6 := by
    have hh := planar_three_many_centres_narrow_gap_witness_count
      hp hcap (by omega : 7 ≤ Fintype.card V)
      hdelta0 hdeltaHalf ht hlam C
    change H.card + 6 ≥ Fintype.card V at hh
    omega
  have hU : (G ∪ H).card ≤ Fintype.card V := by
    simpa using
      (Finset.card_le_card (Finset.subset_univ (G ∪ H)))
  have hSum := Finset.card_union_add_card_inter G H
  have hInter : 0 < (G ∩ H).card := by omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hInter
  have hiG : i ∈ G := (Finset.mem_inter.mp hi).1
  have hiH : i ∈ H := (Finset.mem_inter.mp hi).2
  have hWide : OriginalWideAngleApex p i := by
    apply (mem_originalWideAngleApexFinset p i).1
    simpa only [G] using hiG
  obtain ⟨a, c, hai, hac, hic, hwide⟩ := hWide
  have hupper :
      EuclideanGeometry.angle (p a) (p i) (p c) ≤
        Real.pi - Real.pi / t := by
    simpa [hlam] using (hcap a i c hai hac hic)
  have hexact :
      Real.pi /
        (Real.pi - EuclideanGeometry.angle (p a) (p i) (p c)) -
          3 ≤ delta :=
    three_scale_exact_angle_threshold hdelta0 ht hupper
  have hgap :
      ∃ r : Fin (C i).gaps.length,
        centreQuotient (C i) t r = 0 ∧
        0 < (C i).gaps.get r ∧
        ((Fintype.card V - 4 : ℕ) : ℝ) *
          (t * (C i).gaps.get r) ≤ delta := by
    change i ∈ (Finset.univ : Finset V).filter
      (fun j : V =>
        ∃ r : Fin (C j).gaps.length,
          centreQuotient (C j) t r = 0 ∧
          0 < (C j).gaps.get r ∧
          ((Fintype.card V - 4 : ℕ) : ℝ) *
            (t * (C j).gaps.get r) ≤ delta) at hiH
    exact (Finset.mem_filter.mp hiH).2
  exact ⟨i, ⟨a, c, hai, hac, hic, hwide, hexact⟩, hgap⟩


/-- Global ALL-CARDINALITY original-vertex count at scale 3+delta:
at least N-12 vertices are BOTH strict >120-degree original angle
apices AND original centres with quotient positive support >=3.
This intersection is made from two genuinely different original
geometric packing arguments, without anonymous Boolean resources. -/
theorem planar_three_wide_angle_and_high_support_card_add_twelve
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    Fintype.card V ≤
      ((Finset.univ : Finset V).filter
        (fun i => OriginalWideAngleApex p i ∧
          3 ≤ positiveSupport (centreQuotient (C i) t))).card + 12 := by
  classical
  let G : Finset V := originalWideAngleApexFinset p
  let H : Finset V := (Finset.univ : Finset V).filter
    (fun i => 3 ≤ positiveSupport (centreQuotient (C i) t))
  have hG : Fintype.card V ≤ G.card + 6 :=
    original_many_wide_angle_apices p hp
  have hH : Fintype.card V ≤ H.card + 6 := by
    have hh := planar_three_high_support_card_add_six_ge_total
      hp hcap hdelta0 hdeltaHalf ht hlam C
    change H.card + 6 ≥ Fintype.card V at hh
    omega
  have hU : (G ∪ H).card ≤ Fintype.card V := by
    simpa using (Finset.card_le_card (Finset.subset_univ (G ∪ H)))
  have hCount := Finset.card_union_add_card_inter G H
  have hEq : G ∩ H =
      (Finset.univ : Finset V).filter
        (fun i => OriginalWideAngleApex p i ∧
          3 ≤ positiveSupport (centreQuotient (C i) t)) := by
    ext i
    simp [G, H]
  rw [hEq] at hCount
  omega

/-- For N>=13 there is a single ORIGINAL vertex satisfying three
independent authentic geometric properties:
(1) it is an original >120-degree angle apex with its EXACT
    angular excess bound;
(2) its REAL centre quotient has support exactly three and exponent
    exactly zero (all three positive quotient entries are units);
(3) one original zero-quotient positive projective gap at that SAME
    centre is <= delta / ((N-4)*t).

The statement is a necessary original AngleCap configuration shape,
NOT a certificate paying any of the eight global Boolean debt classes. -/
theorem planar_three_thirteen_centres_joint_zero_exponent_rigidity
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hcard : 13 ≤ Fintype.card V)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    ∃ i : V,
      centreExponent (C i) t = 0 ∧
      positiveSupport (centreQuotient (C i) t) = 3 ∧
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
          (t * (C i).gaps.get r) ≤ delta) := by
  classical
  let S : Finset V := (Finset.univ : Finset V).filter
    (fun i => OriginalWideAngleApex p i ∧
      3 ≤ positiveSupport (centreQuotient (C i) t))
  have hcount : Fintype.card V ≤ S.card + 12 := by
    exact planar_three_wide_angle_and_high_support_card_add_twelve
      hp hcap hdelta0 hdeltaHalf ht hlam C
  have hpos : 0 < S.card := by omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  have hpair : OriginalWideAngleApex p i ∧
      3 ≤ positiveSupport (centreQuotient (C i) t) := by
    exact (Finset.mem_filter.mp hi).2
  obtain ⟨hk, hsupport, _hmass⟩ :=
    three_scale_high_support_exact_rigidity
      (C i) hdelta0 hdeltaHalf ht hpair.2
  obtain ⟨a, c, hai, hac, hic, hwide⟩ := hpair.1
  have hupper :
      EuclideanGeometry.angle (p a) (p i) (p c) ≤
        Real.pi - Real.pi / t := by
    simpa [hlam] using (hcap a i c hai hac hic)
  have hexact := three_scale_exact_angle_threshold hdelta0 ht hupper
  have hgap := planar_three_every_high_support_centre_has_narrow_gap
    hp hcap (by omega : 7 ≤ Fintype.card V)
    hdelta0 hdeltaHalf ht hlam C i hpair.2
  exact ⟨i, hk, hsupport, ⟨a, c, hai, hac, hic, hwide, hexact⟩, hgap⟩

#print axioms planar_three_wide_angle_and_high_support_card_add_twelve
#print axioms planar_three_thirteen_centres_joint_zero_exponent_rigidity

#print axioms planar_three_thirteen_centres_joint_exact_angle_narrow_gap

end JSP000404Research
