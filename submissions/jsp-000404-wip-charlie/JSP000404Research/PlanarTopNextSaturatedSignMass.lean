import JSP000404Research.PlanarTopNextTripleTransitionsMultiplicity
import JSP000404Research.PlanarSupportThreeActualSaturatedSignChanges
import Mathlib.Tactic

/-!
# Original n=3 top+next forces N-4 centres with full positive sign saturation

The source-native top+next strict-support packing excludes two distinct
one-transition centres. Its exact global multiplicity theorem shows that
at least N-4 original support-three centres have THREE canonical sign
transitions. At each such genuine original centre, the independently
checked saturation theorem proves ALL three positive original quotient
positions are actual sign transitions, not merely potential candidates.

This produces a cardinality-controlled original geometric sign
constraint. It neither gives distinct TRUE exterior Boolean words
nor pays the still-open unrestricted eight-class source debt.
-/

namespace JSP000404Research

open Classical

/-- With an original n=3 exponent-two top and distinct support-one
exponent-one next centre, at least N-4 original centres have support
exactly three and use ALL positive projective quotient gaps as sign
transition slots in the actual canonical lifted signed-ray cycle. -/
theorem planar_three_top_next_exact_sign_saturated_card_add_four_ge_total
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
    Fintype.card V ≤
      ((Finset.univ : Finset V).filter
        (fun i =>
          positiveSupport (centreQuotient (C i) t) = 3 ∧
          ∃ first : OtherVertex i,
            ∃ rest : List (OtherVertex i),
              (C i).rays = first :: rest ∧
              ChangesExactlyOnPositive
                (raySignAt hp i first)
                (liftedCentreSignPath hp i first rest)
                (quotientList t (C i).gaps))).card + 4 := by
  classical
  let T : Finset V := Finset.univ.filter
    (fun i =>
      positiveSupport (centreQuotient (C i) t) = 3 ∧
      HasActualSignTransitions hp (C i) 3)
  let U : Finset V := Finset.univ.filter
    (fun i =>
      positiveSupport (centreQuotient (C i) t) = 3 ∧
      ∃ first : OtherVertex i,
        ∃ rest : List (OtherVertex i),
          (C i).rays = first :: rest ∧
          ChangesExactlyOnPositive
            (raySignAt hp i first)
            (liftedCentreSignPath hp i first rest)
            (quotientList t (C i).gaps))
  have hT : Fintype.card V ≤ T.card + 4 := by
    simpa only [T] using
      (planar_three_top_next_triple_transitions_card_add_four_ge_total
        hp hcap hdelta0 hdeltaHalf ht hlam C hsa hs ha hsupA)
  have htpos : 0 < t :=
    sendov_scale_pos (by decide : 1 ≤ (3 : ℕ)) hdelta0 ht
  have htone : 1 ≤ t :=
    sendov_scale_one_le (by decide : 1 ≤ (3 : ℕ)) hdelta0 ht
  have hsub : T ⊆ U := by
    intro i hi
    obtain ⟨hsup, hthreeW⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨first, rest, hrays, hthree⟩ := hthreeW
    have hsat :
        ChangesExactlyOnPositive
          (raySignAt hp i first)
          (liftedCentreSignPath hp i first rest)
          (quotientList t (C i).gaps) :=
      support_three_triple_transition_changes_exactly_on_positive
        hp hcap htpos htone hlam i (C i)
        hsup first rest hrays hthree
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨hsup, ⟨first,rest,hrays,hsat⟩⟩⟩
  have hcount := Finset.card_le_card hsub
  change Fintype.card V ≤ U.card + 4
  omega

/-- In particular N>=7 forces at least THREE distinct genuinely
sign-saturated support-three original centres under the top+next
configuration. This is NOT three separate Boolean hole credits. -/
theorem planar_three_seven_top_next_forces_three_exact_sign_saturated_centres
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
        ∃ first : OtherVertex i,
          ∃ rest : List (OtherVertex i),
            (C i).rays = first :: rest ∧
            ChangesExactlyOnPositive
              (raySignAt hp i first)
              (liftedCentreSignPath hp i first rest)
              (quotientList t (C i).gaps))).card := by
  have h :=
    planar_three_top_next_exact_sign_saturated_card_add_four_ge_total
      hp hcap hdelta0 hdeltaHalf ht hlam
      C hsa hs ha hsupA
  omega

#print axioms planar_three_top_next_exact_sign_saturated_card_add_four_ge_total
#print axioms planar_three_seven_top_next_forces_three_exact_sign_saturated_centres

end JSP000404Research
