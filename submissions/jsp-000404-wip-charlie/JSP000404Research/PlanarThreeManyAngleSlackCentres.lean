import JSP000404Research.PlanarThreeSevenAngleSlackBarrier
import Mathlib.Tactic

/-!
# Genuine multiplicity of sharp-angle centres and their strip-slack witnesses

The kernel-proved seven-point >120-degree theorem has a stronger
multiplicity consequence: if a finite injective planar configuration
has N points, then at least N-6 DISTINCT ORIGINAL VERTICES are apices
of some original angle strictly exceeding 120 degrees.

Indeed, otherwise the set of all vertices that are *not* such apices
would contain seven points, contradicting the already-certified
seven-point theorem when restricted to that original subset.

Under actual n=3 AngleCap geometry every such angular excess is paid
by the *local* strip-slack inequality

  3*t*(angle - (pi-pi/3)) <= pi*delta.

Importantly, these are N-6 distinct real centre witnesses, NOT a single
shared delta budget: each has its own angle inequality. No Boolean
true exterior hole or eight-source nonreusing payment is inferred.
-/

namespace JSP000404Research

/-- An original vertex is a strict >120-degree angle apex for some
other two ORIGINAL distinct vertices. -/
def OriginalWideAngleApex
    {V : Type*} (p : V → Plane) (i : V) : Prop :=
  ∃ a c : V, a ≠ i ∧ a ≠ c ∧ i ≠ c ∧
    Real.pi - Real.pi / 3 <
      EuclideanGeometry.angle (p a) (p i) (p c)

/-- ALL finite injective original planar point sets have at least
N-6 distinct original >120-degree angle apex vertices. -/
theorem original_many_wide_angle_apices
    {V : Type*} [LinearOrder V] [Fintype V]
    (p : V → Plane)
    (hp : Function.Injective p) :
    Fintype.card V ≤
      ((Finset.univ : Finset V).filter
        (OriginalWideAngleApex p)).card + 6 := by
  classical
  let G : Finset V :=
    (Finset.univ : Finset V).filter (OriginalWideAngleApex p)
  let B : Finset V :=
    (Finset.univ : Finset V).filter (fun i => ¬ OriginalWideAngleApex p i)
  have hB : B.card ≤ 6 := by
    by_contra hnot
    have hbseven : 7 ≤ B.card := by omega
    have hsubcard : 7 ≤ Fintype.card (↥B) := by
      simpa using hbseven
    let q : (↥B) → Plane := fun i => p i.1
    have hqinj : Function.Injective q := by
      intro x y heq
      apply Subtype.ext
      exact hp heq
    obtain ⟨a, b, c, hab, hac, hbc, hwide⟩ :=
      seven_points_have_actual_angle_gt_two_pi_over_three q hqinj hsubcard
    have hwideB : OriginalWideAngleApex p b.1 := by
      refine ⟨a.1, c.1, ?_, ?_, ?_, ?_⟩
      · intro h
        exact hab (Subtype.ext h)
      · intro h
        exact hac (Subtype.ext h)
      · intro h
        exact hbc (Subtype.ext h)
      · exact hwide
    have hbnot : ¬ OriginalWideAngleApex p b.1 :=
      (Finset.mem_filter.mp b.2).2
    exact hbnot hwideB
  have hCover : G ∪ B = (Finset.univ : Finset V) := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact (em (OriginalWideAngleApex p i)).symm
  have hsum : Fintype.card V ≤ G.card + B.card := by
    calc
      Fintype.card V = (G ∪ B).card := by simp [hCover]
      _ ≤ G.card + B.card := Finset.card_union_le G B
  change Fintype.card V ≤ G.card + 6
  omega

/-- Each original wide-angle apex has a real strip-slack angular
certificate under the ORIGINAL n=3 AngleCap hypotheses. -/
theorem original_wide_angle_apex_has_paid_strip_witness
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hcap : AngleCap p lam)
    {t delta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {i : V}
    (hi : OriginalWideAngleApex p i) :
    ∃ a c : V,
      a ≠ i ∧ a ≠ c ∧ i ≠ c ∧
      Real.pi - Real.pi / 3 <
        EuclideanGeometry.angle (p a) (p i) (p c) ∧
      3 * t *
        (EuclideanGeometry.angle (p a) (p i) (p c) -
          (Real.pi - Real.pi / 3)) ≤ Real.pi * delta := by
  obtain ⟨a, c, hai, hac, hic, hlarge⟩ := hi
  have hupper :
      EuclideanGeometry.angle (p a) (p i) (p c) ≤
        Real.pi - Real.pi / t := by
    simpa [hlam] using (hcap a i c hai hac hic)
  exact ⟨a, c, hai, hac, hic, hlarge,
    three_scale_angle_excess_le_strip_slack hdelta0 ht hupper⟩

/-- At least N-6 ORIGINAL vertices each admit a genuine positive
angle excess and their OWN strip-slack inequality. -/
theorem planar_three_many_paid_wide_angle_centres
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t) :
    Fintype.card V ≤
      ((Finset.univ : Finset V).filter
        (fun i : V =>
          ∃ a c : V,
            a ≠ i ∧ a ≠ c ∧ i ≠ c ∧
            Real.pi - Real.pi / 3 <
              EuclideanGeometry.angle (p a) (p i) (p c) ∧
            3 * t *
              (EuclideanGeometry.angle (p a) (p i) (p c) -
                (Real.pi - Real.pi / 3)) ≤ Real.pi * delta)).card + 6 := by
  classical
  let G : Finset V :=
    (Finset.univ : Finset V).filter (OriginalWideAngleApex p)
  let P : Finset V :=
    (Finset.univ : Finset V).filter
      (fun i : V =>
        ∃ a c : V,
          a ≠ i ∧ a ≠ c ∧ i ≠ c ∧
          Real.pi - Real.pi / 3 <
            EuclideanGeometry.angle (p a) (p i) (p c) ∧
          3 * t *
            (EuclideanGeometry.angle (p a) (p i) (p c) -
              (Real.pi - Real.pi / 3)) ≤ Real.pi * delta)
  have hsub : G ⊆ P := by
    intro i hi
    have hwi : OriginalWideAngleApex p i :=
      (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ i,
        original_wide_angle_apex_has_paid_strip_witness
          hcap hdelta0 ht hlam hwi⟩
  have hg : Fintype.card V ≤ G.card + 6 := by
    simpa only [G] using original_many_wide_angle_apices p hp
  have hc : G.card ≤ P.card := Finset.card_le_card hsub
  change Fintype.card V ≤ P.card + 6
  omega

#print axioms original_many_wide_angle_apices
#print axioms original_wide_angle_apex_has_paid_strip_witness
#print axioms planar_three_many_paid_wide_angle_centres

end JSP000404Research
