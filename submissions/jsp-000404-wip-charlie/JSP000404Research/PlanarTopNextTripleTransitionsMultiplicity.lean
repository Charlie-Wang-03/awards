import JSP000404Research.PlanarTopNextForcesThreeTransitions
import JSP000404Research.PlanarThreeTopNextSupportOnePacking
import JSP000404Research.ThreeFiveSupportThreeRigidity
import JSP000404Research.PlanarThreeCrowdedTopTinyGap
import Mathlib.Tactic

/-!
# Three distinct original high-support centres must flip three times

In an n=3 AngleCap original configuration with >=7 vertices,
a genuine top exponent-two and a distinct support-one next exponent-one
centre force at least FOUR high-support exponent-zero centres.
The strict-support angular packing theorem from the previous module
prohibits any TWO further genuinely one-transition centres.

At EACH high-support original centre the canonical sign path has
exactly one OR exactly three sign transitions, by the independently
certified support-three dichotomy. Hence at least THREE distinct
high-support centres must be in the three-transition branch.

This is ORIGINAL geometry and ACTUAL signed-ray transitions; it is NOT
a disjoint family of true Boolean exterior holes, nor a closure of
the unrestricted eight-class source payment.
-/

namespace JSP000404Research

open Classical

/-- The actual sign transition count of the canonical projective ray
cycle, witnessed using its FIRST REAL ray and remaining ordered rays. -/
def HasActualSignTransitions
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {i : V} (C : CentreProjectiveCycle hp i) (m : ℕ) : Prop :=
  ∃ first : OtherVertex i,
    ∃ rest : List (OtherVertex i),
      C.rays = first :: rest ∧
      boolTransitionCountFrom
        (raySignAt hp i first)
        (liftedCentreSignPath hp i first rest) = m

/-- With one original top and one original support-one next centre,
at most ONE other original centre can have a one-transition canonical
sign path. Its quotient support is NOT assumed small. -/
theorem planar_three_top_next_other_one_transition_card_le_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {s a : V} (hsa : s ≠ a)
    (hs : centreExponent (C s) t = 2)
    (ha : centreExponent (C a) t = 1)
    (hsupA : positiveSupport (centreQuotient (C a) t) = 1) :
    ((Finset.univ : Finset V).filter
      (fun i => i ≠ s ∧ i ≠ a ∧
        HasActualSignTransitions hp (C i) 1)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro b hb c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb hc
  by_contra hbc
  obtain ⟨fb, rb, hbr, htransB⟩ := hb.2.2
  obtain ⟨fc, rc, hcr, htransC⟩ := hc.2.2
  exact planar_three_top_next_no_two_one_transition_centres
    hp hcap hdelta0 hdeltaHalf ht hlam
    hsa hb.1.symm hc.1.symm hb.2.1.symm hc.2.1.symm hbc
    (C s) (C a) (C b) (C c)
    hs ha hsupA fb rb hbr htransB fc rc hcr htransC

/-- The sharpened ACTUAL seven-centre top+next geometry has at
least THREE distinct original support-three centres, each with
exactly three genuine canonical sign transitions. No Boolean-hole
existence, source matching or extra geometric hypothesis is assumed. -/
theorem planar_three_top_next_triple_transitions_card_add_four_ge_total
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {s a : V} (hsa : s ≠ a)
    (hs : centreExponent (C s) t = 2)
    (ha : centreExponent (C a) t = 1)
    (hsupA : positiveSupport (centreQuotient (C a) t) = 1) :
    Fintype.card V ≤ ((Finset.univ : Finset V).filter
      (fun i =>
        positiveSupport (centreQuotient (C i) t) = 3 ∧
        HasActualSignTransitions hp (C i) 3)).card + 4 := by
  classical
  let H : Finset V := Finset.univ.filter
    (fun i => 3 ≤ positiveSupport (centreQuotient (C i) t))
  let E : Finset V := Finset.univ.filter
    (fun i => i ≠ s ∧ i ≠ a ∧
      HasActualSignTransitions hp (C i) 1)
  let T : Finset V := Finset.univ.filter
    (fun i => positiveSupport (centreQuotient (C i) t) = 3 ∧
      HasActualSignTransitions hp (C i) 3)
  have hH : Fintype.card V ≤ H.card + 3 := by
    simpa only [H] using
      (planar_three_top_next_support_one_forces_high_support_plus_three
        hp hcap hdelta0 hdeltaHalf ht hlam
        C s a hs ha hsupA)
  have hE : E.card ≤ 1 := by
    simpa only [E] using
      (planar_three_top_next_other_one_transition_card_le_one
        hp hcap hdelta0 hdeltaHalf ht hlam
        C hsa hs ha hsupA)
  have htpos : 0 < t :=
    sendov_scale_pos (by decide : 1 ≤ (3 : ℕ)) hdelta0 ht
  have htone : 1 ≤ t :=
    sendov_scale_one_le (by decide : 1 ≤ (3 : ℕ)) hdelta0 ht
  have hsTop :
      positiveSupport (centreQuotient (C s) t) = 1 :=
    (planar_three_top_centre_has_exact_unit_support
      (C s) hdelta0 hdeltaHalf ht hs).1
  have hcovered : H ⊆ E ∪ T := by
    intro i hi
    have hi3 : 3 ≤ positiveSupport (centreQuotient (C i) t) :=
      (Finset.mem_filter.mp hi).2
    have hsup3 : positiveSupport (centreQuotient (C i) t) = 3 :=
      (three_scale_high_support_exact_rigidity
        (C i) hdelta0 hdeltaHalf ht hi3).2.1
    obtain ⟨first,rest,hrays,hcase⟩ :=
      support_three_transition_count_one_or_three
        hp hcap htpos htone hlam i (C i) hsup3
    rcases hcase with hone | hthree
    · have his : i ≠ s := by
        intro h
        rw [h] at hsup3
        omega
      have hia : i ≠ a := by
        intro h
        rw [h] at hsup3
        omega
      apply Finset.mem_union.mpr
      left
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ⟨his,hia,⟨first,rest,hrays,hone⟩⟩⟩
    · apply Finset.mem_union.mpr
      right
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ⟨hsup3,⟨first,rest,hrays,hthree⟩⟩⟩
  have hcapCount : H.card ≤ E.card + T.card := by
    calc
      H.card ≤ (E ∪ T).card := Finset.card_le_card hcovered
      _ ≤ E.card + T.card := Finset.card_union_le E T
  change Fintype.card V ≤ T.card + 4
  omega


/-- The original seven-centre corollary from the quantitative
all-cardinality trichotomy.  Four or more genuinely three-transition
original centres are NOT asserted to be disjoint Boolean hole credits. -/
theorem planar_three_seven_top_next_forces_three_triple_transition_centres
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hseven : 7 ≤ Fintype.card V)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {s a : V} (hsa : s ≠ a)
    (hs : centreExponent (C s) t = 2)
    (ha : centreExponent (C a) t = 1)
    (hsupA : positiveSupport (centreQuotient (C a) t) = 1) :
    3 ≤ ((Finset.univ : Finset V).filter
      (fun i =>
        positiveSupport (centreQuotient (C i) t) = 3 ∧
        HasActualSignTransitions hp (C i) 3)).card := by
  have h := planar_three_top_next_triple_transitions_card_add_four_ge_total
    hp hcap hdelta0 hdeltaHalf ht hlam C hsa hs ha hsupA
  omega


#print axioms planar_three_top_next_other_one_transition_card_le_one
#print axioms planar_three_top_next_triple_transitions_card_add_four_ge_total
#print axioms planar_three_seven_top_next_forces_three_triple_transition_centres

end JSP000404Research
