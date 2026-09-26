import JSP000404Research.TriangleCriticalTransitionSeed
import JSP000404Research.TransitionUnitGapSlot
import Mathlib.Tactic

/-!
# Ordinary short triangle arcs produce concrete global unit-transition slots

Combine two previously independent steps:

1. TriangleCriticalTransitionSeed:
   if the three unoriented projective edge directions of a triangle lie in one
   ordinary lifted interval of width S, triangle sign parity plus the global
   angle cap finds a transition pair of width in [1,S].

2. TransitionUnitGapSlot:
   any transition pair of width at most 1+delta refines to an actual adjacent
   q=1 transition gap and hence a concrete GlobalUnitGapSlot.

Therefore every ordinary triangle direction arc of width at most 1+delta
produces a terminal unit-transition slot at one of its three vertices.
-/

namespace JSP000404Research

open Real

theorem triangle_ordinary_arc_has_global_unit_transition_slot
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    {lam t delta L S : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hSTop : S ≤ 1 + delta)
    {i j k : V}
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k)
    (hijArc :
      L ≤ normalizedEdgeTheta hp t i j hij ∧
      normalizedEdgeTheta hp t i j hij ≤ L + S)
    (hikArc :
      L ≤ normalizedEdgeTheta hp t i k hik ∧
      normalizedEdgeTheta hp t i k hik ≤ L + S)
    (hjkArc :
      L ≤ normalizedEdgeTheta hp t j k hjk ∧
      normalizedEdgeTheta hp t j k hjk ≤ L + S) :
    ∃ u : GlobalUnitGapSlot C t,
      (u.1 = i ∨ u.1 = j ∨ u.1 = k) ∧
      GlobalUnitGapOrdinaryTransition C t u := by
  have hseed :=
    triangle_has_critical_transition_seed_in_ordinary_arc
      hp hcap ht hlam hij hik hjk
      hijArc hikArc hjkArc
  rcases hseed with hi | hj | hk
  · let ji : OtherVertex i := ⟨j, hij.symm⟩
    let ki : OtherVertex i := ⟨k, hik.symm⟩
    have hwidth :
        t * (|rayThetaAt hp i ji -
              rayThetaAt hp i ki| / Real.pi)
          ≤ 1 + delta := by
      have heq :=
        abs_normalizedEdgeTheta_sub_eq_scaled_abs_theta
          hp ht.le i hij hik
      rw [heq] at hi
      exact hi.2.2.trans hSTop
    have hjki : ji ≠ ki := by
      intro h
      apply hjk
      exact congrArg Subtype.val h
    obtain ⟨u, hui, huTrans⟩ :=
      exists_global_unit_ordinary_transition_slot_between_rays
        C hcap ht hlam hdeltaHalf i
        hjki hi.1 hwidth
    exact ⟨u, Or.inl hui, huTrans⟩
  · let ijj : OtherVertex j := ⟨i, hij⟩
    let kj : OtherVertex j := ⟨k, hjk.symm⟩
    have hwidth :
        t * (|rayThetaAt hp j ijj -
              rayThetaAt hp j kj| / Real.pi)
          ≤ 1 + delta := by
      have heq :
          |normalizedEdgeTheta hp t i j hij -
              normalizedEdgeTheta hp t j k hjk|
            =
          t * (|rayThetaAt hp j ijj -
              rayThetaAt hp j kj| / Real.pi) := by
        rw [normalizedEdgeTheta_reverse hp t hij]
        simpa [ijj, kj] using
          abs_normalizedEdgeTheta_sub_eq_scaled_abs_theta
            hp ht.le j hij.symm hjk
      rw [← heq]
      exact hj.2.2.trans hSTop
    have hne : ijj ≠ kj := by
      intro h
      apply hik
      exact congrArg Subtype.val h
    obtain ⟨u, hui, huTrans⟩ :=
      exists_global_unit_ordinary_transition_slot_between_rays
        C hcap ht hlam hdeltaHalf j
        hne hj.1 hwidth
    exact ⟨u, Or.inr (Or.inl hui), huTrans⟩
  · let ik : OtherVertex k := ⟨i, hik⟩
    let jk : OtherVertex k := ⟨j, hjk⟩
    have hwidth :
        t * (|rayThetaAt hp k ik -
              rayThetaAt hp k jk| / Real.pi)
          ≤ 1 + delta := by
      have heq :
          |normalizedEdgeTheta hp t i k hik -
              normalizedEdgeTheta hp t j k hjk|
            =
          t * (|rayThetaAt hp k ik -
              rayThetaAt hp k jk| / Real.pi) := by
        rw [normalizedEdgeTheta_reverse hp t hik,
            normalizedEdgeTheta_reverse hp t hjk]
        simpa [ik, jk] using
          abs_normalizedEdgeTheta_sub_eq_scaled_abs_theta
            hp ht.le k hik.symm hjk.symm
      rw [← heq]
      exact hk.2.2.trans hSTop
    have hne : ik ≠ jk := by
      intro h
      apply hij
      exact congrArg Subtype.val h
    obtain ⟨u, hui, huTrans⟩ :=
      exists_global_unit_ordinary_transition_slot_between_rays
        C hcap ht hlam hdeltaHalf k
        hne hk.1 hwidth
    exact ⟨u, Or.inr (Or.inr hui), huTrans⟩

#print axioms triangle_ordinary_arc_has_global_unit_transition_slot

end JSP000404Research
