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

#print axioms planar_three_thirteen_centres_joint_exact_angle_narrow_gap

end JSP000404Research
