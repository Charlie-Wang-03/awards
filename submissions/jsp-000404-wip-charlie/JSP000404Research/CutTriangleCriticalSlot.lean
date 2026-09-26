import JSP000404Research.CutTransitionSeedCriticalSlot
import JSP000404Research.TriangleSignParity
import Mathlib.Tactic

/-!
# Short cut triangles produce cyclic critical unit obstructions

Use the normalized projective coordinate at one arbitrary cut c on each
unoriented edge.  Reversing an edge preserves its cut coordinate and flips its
cut-adjusted Boolean sign.

Therefore the same Boolean parity as for canonical projective signs holds on
every triangle: at least one vertex sees its two incident cut signs differ.

If all three edge coordinates lie in [0,1+delta], that transition pair is a
short cut-transition seed.  CutTransitionSeedCriticalSlot then produces a
canonical global q=1 slot obstructing the global phase

  t*c/pi + delta.
-/

namespace JSP000404Research

noncomputable def cutNormalizedEdgeTheta
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (t c : ℝ)
    (i j : V)
    (hij : i ≠ j) : ℝ :=
  cutNormalizedRayTheta hp t c i
    (⟨j, hij.symm⟩ : OtherVertex i)

theorem cutNormalizedEdgeTheta_reverse
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (t c : ℝ)
    {i j : V}
    (hij : i ≠ j) :
    cutNormalizedEdgeTheta hp t c i j hij =
      cutNormalizedEdgeTheta hp t c j i hij.symm := by
  unfold cutNormalizedEdgeTheta cutNormalizedRayTheta
  rw [cutRayTheta_reverse_eq hp c hij]

/-- Triangle parity specialized to cut-adjusted signs. -/
theorem triangle_exactly_one_other_cutSign_transition
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (c : ℝ)
    {i j k : V}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi :
      cutRaySign hp c i ⟨j, hij.symm⟩ =
        cutRaySign hp c i ⟨k, hik.symm⟩) :
    (
      cutRaySign hp c j ⟨i, hij⟩ ≠
        cutRaySign hp c j ⟨k, hjk.symm⟩
    ) ∧
      ¬ (
        cutRaySign hp c k ⟨i, hik⟩ ≠
          cutRaySign hp c k ⟨j, hjk⟩
      )
    ∨
    ¬ (
      cutRaySign hp c j ⟨i, hij⟩ ≠
        cutRaySign hp c j ⟨k, hjk.symm⟩
    ) ∧
      (
        cutRaySign hp c k ⟨i, hik⟩ ≠
          cutRaySign hp c k ⟨j, hjk⟩
      ) := by
  have hji :=
    cutRaySign_reverse_eq_not hp c hij
  have hki :=
    cutRaySign_reverse_eq_not hp c hik
  have hkj :=
    cutRaySign_reverse_eq_not hp c hjk
  let sij :=
    cutRaySign hp c i ⟨j, hij.symm⟩
  let sik :=
    cutRaySign hp c i ⟨k, hik.symm⟩
  let sjk :=
    cutRaySign hp c j ⟨k, hjk.symm⟩
  have hpure :=
    exactly_one_other_transition_of_same_at_first
      (sij := sij) (sik := sik) (sjk := sjk)
      (by simpa [sij, sik] using hi)
  dsimp [sij, sik, sjk] at hpure
  rw [hji, hki] at hpure
  have hkj' :
      cutRaySign hp c k ⟨j, hjk⟩ =
        !cutRaySign hp c j ⟨k, hjk.symm⟩ := hkj
  rw [hkj'] at hpure
  exact hpure

/-- Main short-triangle obstruction at an arbitrary cut. -/
theorem cut_triangle_short_arc_has_cyclic_critical_slot
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    {lam t delta c : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi)
    {i j k : V}
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k)
    (hijArc :
      0 ≤ cutNormalizedEdgeTheta hp t c i j hij ∧
      cutNormalizedEdgeTheta hp t c i j hij ≤ 1 + delta)
    (hikArc :
      0 ≤ cutNormalizedEdgeTheta hp t c i k hik ∧
      cutNormalizedEdgeTheta hp t c i k hik ≤ 1 + delta)
    (hjkArc :
      0 ≤ cutNormalizedEdgeTheta hp t c j k hjk ∧
      cutNormalizedEdgeTheta hp t c j k hjk ≤ 1 + delta) :
    ∃ u : GlobalUnitGapSlot C t,
      (u.1 = i ∨ u.1 = j ∨ u.1 = k) ∧
      GlobalCyclicCriticalUnitBadAt
        C t delta u (t * c / Real.pi + delta) := by
  let sij :=
    cutRaySign hp c i
      (⟨j, hij.symm⟩ : OtherVertex i)
  let sik :=
    cutRaySign hp c i
      (⟨k, hik.symm⟩ : OtherVertex i)
  by_cases hi : sij ≠ sik
  · have hijArcI :
        0 ≤ cutNormalizedRayTheta hp t c i
              (⟨j, hij.symm⟩ : OtherVertex i) ∧
        cutNormalizedRayTheta hp t c i
              (⟨j, hij.symm⟩ : OtherVertex i) ≤ 1 + delta := by
      simpa [cutNormalizedEdgeTheta] using hijArc
    have hikArcI :
        0 ≤ cutNormalizedRayTheta hp t c i
              (⟨k, hik.symm⟩ : OtherVertex i) ∧
        cutNormalizedRayTheta hp t c i
              (⟨k, hik.symm⟩ : OtherVertex i) ≤ 1 + delta := by
      simpa [cutNormalizedEdgeTheta] using hikArc
    obtain ⟨u, hui, hubad⟩ :=
      cut_transition_seed_has_cyclic_critical_slot
        hp hcap C ht hlam hdeltaHalf hc0 hcpi
        i
        (by
          intro h
          apply hjk
          exact congrArg Subtype.val h)
        (by simpa [sij, sik] using hi)
        hijArcI hikArcI
    exact ⟨u, Or.inl hui, hubad⟩
  · have hiEq : sij = sik := not_ne_iff.mp hi
    have hpar :=
      triangle_exactly_one_other_cutSign_transition
        hp c hij hik hjk
        (by simpa [sij, sik] using hiEq)
    rcases hpar with hjTrans | hkTrans
    · have hjiArc :
          0 ≤ cutNormalizedRayTheta hp t c j
                (⟨i, hij⟩ : OtherVertex j) ∧
          cutNormalizedRayTheta hp t c j
                (⟨i, hij⟩ : OtherVertex j) ≤ 1 + delta := by
        rw [← cutNormalizedEdgeTheta_reverse hp t c hij]
        simpa [cutNormalizedEdgeTheta] using hijArc
      have hjkArcJ :
          0 ≤ cutNormalizedRayTheta hp t c j
                (⟨k, hjk.symm⟩ : OtherVertex j) ∧
          cutNormalizedRayTheta hp t c j
                (⟨k, hjk.symm⟩ : OtherVertex j) ≤ 1 + delta := by
        simpa [cutNormalizedEdgeTheta] using hjkArc
      obtain ⟨u, huj, hubad⟩ :=
        cut_transition_seed_has_cyclic_critical_slot
          hp hcap C ht hlam hdeltaHalf hc0 hcpi
          j
          (by
            intro h
            apply hik
            exact congrArg Subtype.val h)
          hjTrans.1
          hjiArc hjkArcJ
      exact ⟨u, Or.inr (Or.inl huj), hubad⟩
    · have hkiArc :
          0 ≤ cutNormalizedRayTheta hp t c k
                (⟨i, hik⟩ : OtherVertex k) ∧
          cutNormalizedRayTheta hp t c k
                (⟨i, hik⟩ : OtherVertex k) ≤ 1 + delta := by
        rw [← cutNormalizedEdgeTheta_reverse hp t c hik]
        simpa [cutNormalizedEdgeTheta] using hikArc
      have hkjArc :
          0 ≤ cutNormalizedRayTheta hp t c k
                (⟨j, hjk⟩ : OtherVertex k) ∧
          cutNormalizedRayTheta hp t c k
                (⟨j, hjk⟩ : OtherVertex k) ≤ 1 + delta := by
        rw [← cutNormalizedEdgeTheta_reverse hp t c hjk]
        simpa [cutNormalizedEdgeTheta] using hjkArc
      obtain ⟨u, huk, hubad⟩ :=
        cut_transition_seed_has_cyclic_critical_slot
          hp hcap C ht hlam hdeltaHalf hc0 hcpi
          k
          (by
            intro h
            apply hij
            exact congrArg Subtype.val h)
          hkTrans.2
          hkiArc hkjArc
      exact ⟨u, Or.inr (Or.inr huk), hubad⟩

#print axioms cutNormalizedEdgeTheta_reverse
#print axioms triangle_exactly_one_other_cutSign_transition
#print axioms cut_triangle_short_arc_has_cyclic_critical_slot

end JSP000404Research
