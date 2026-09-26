import JSP000404Research.OrdinaryCriticalUnitObstruction
import JSP000404Research.TriangleCriticalTransitionSeed
import JSP000404Research.CentreTransitionRefinement
import JSP000404Research.TransitionUnitGapSlot
import JSP000404Research.CriticalPhaseDomination
import Mathlib.Tactic

/-!
# Domination of an ordinary triangle obstruction by a concrete unit transition

The previous modules prove the ingredients separately:

* an ordinary short triangle-direction arc contains an opposite-sign
  transition seed;
* every ordered transition seed refines to an adjacent transition gap;
* in the lower branch, an adjacent transition gap of width at most 1+delta
  has quotient exactly one;
* a nested critical gap has a bad-phase interval containing the parent arc's
  bad-phase interval.

This file retains the nesting data all the way to the concrete
GlobalUnitGapSlot.  It closes the local bridge

  parent ordinary triangle bad phase
      -> OrdinaryCriticalUnitBadAt.

No global phase-cover assumption is used here.
-/

namespace JSP000404Research

open Real

/-- Ordered two-ray version retaining the parent-arc nesting data. -/
theorem ordered_transition_seed_parent_bad_has_critical_unit
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    {lam t delta L S x : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hSTop : S ≤ 1 + delta)
    (i : V)
    {j k : OtherVertex i}
    (hjk : j ≠ k)
    (htheta : rayThetaAt hp i j < rayThetaAt hp i k)
    (hsign : raySignAt hp i j ≠ raySignAt hp i k)
    (hjArc :
      L ≤ normalizedRayTheta hp t i j ∧
      normalizedRayTheta hp t i j ≤ L + S)
    (hkArc :
      L ≤ normalizedRayTheta hp t i k ∧
      normalizedRayTheta hp t i k ≤ L + S)
    (hx :
      arcBadLeft L S ≤ x ∧
      x ≤ arcBadRight L delta) :
    ∃ u : GlobalUnitGapSlot C t,
      u.1 = i ∧
      OrdinaryCriticalUnitBadAt C t delta u x := by
  obtain ⟨q, r, hsucc, hjLeQ, hrLeK,
      htrans, hlow, hseedLe⟩ :=
    (C i).exists_adjacent_transition_inside_ordered_seed
      hcap ht hlam htheta hsign

  have hthetaJQ :
      rayThetaAt hp i j ≤
        rayThetaAt hp i ((C i).rays.get q) := by
    have h := (C i).theta_le_of_rayIndex_le hjLeQ
    simpa [(C i).get_rayIndex] using h
  have hthetaRK :
      rayThetaAt hp i ((C i).rays.get r) ≤
        rayThetaAt hp i k := by
    have h := (C i).theta_le_of_rayIndex_le hrLeK
    simpa [(C i).get_rayIndex] using h

  have hscale0 : 0 ≤ t / Real.pi := by
    exact div_nonneg ht.le Real.pi_pos.le

  have hnormJQ :
      normalizedRayTheta hp t i j ≤
        normalizedRayTheta hp t i ((C i).rays.get q) := by
    unfold normalizedRayTheta
    have h :=
      mul_le_mul_of_nonneg_left hthetaJQ hscale0
    convert h using 1 <;> ring

  have hnormRK :
      normalizedRayTheta hp t i ((C i).rays.get r) ≤
        normalizedRayTheta hp t i k := by
    unfold normalizedRayTheta
    have h :=
      mul_le_mul_of_nonneg_left hthetaRK hscale0
    convert h using 1 <;> ring

  let alpha :=
    normalizedRayTheta hp t i ((C i).rays.get q)
  let s :=
    t * ((rayThetaAt hp i ((C i).rays.get r) -
      rayThetaAt hp i ((C i).rays.get q)) / Real.pi)

  have halpha : L ≤ alpha := by
    dsimp [alpha]
    exact hjArc.1.trans hnormJQ

  have halphaAdd :
      alpha + s =
        normalizedRayTheta hp t i ((C i).rays.get r) := by
    dsimp [alpha, s, normalizedRayTheta]
    ring

  have hright : alpha + s ≤ L + S := by
    rw [halphaAdd]
    exact hnormRK.trans hkArc.2

  have hseedTop :
      t * ((rayThetaAt hp i k -
          rayThetaAt hp i j) / Real.pi) ≤ S := by
    have hdiff :
        normalizedRayTheta hp t i k -
            normalizedRayTheta hp t i j ≤ S := by
      linarith [hjArc.1, hkArc.2]
    unfold normalizedRayTheta at hdiff
    convert hdiff using 1 <;> ring

  have hsTopS : s ≤ S := by
    exact hseedLe.trans hseedTop
  have hsTop : s ≤ 1 + delta :=
    hsTopS.trans hSTop
  have hfloor : Nat.floor s = 1 :=
    critical_gap_floor_eq_one hdeltaHalf hlow hsTop

  have hm : q.val + 1 < (C i).rays.length := by
    rw [← hsucc]
    exact r.isLt
  have hrEq :
      r = ⟨q.val + 1, hm⟩ := by
    apply Fin.ext
    exact hsucc
  have hfloor' :
      Nat.floor
        (t * ((rayThetaAt hp i
            ((C i).rays.get ⟨q.val + 1, hm⟩) -
          rayThetaAt hp i
            ((C i).rays.get ⟨q.val, q.isLt⟩)) / Real.pi)) = 1 := by
    rw [← hrEq]
    exact hfloor

  obtain ⟨uLocal, huval⟩ :=
    exists_centreUnitGap_of_adjacent_floor_one
      (C i) t q.val hm hfloor'
  let u : GlobalUnitGapSlot C t := ⟨i, uLocal⟩

  have hxCritical :
      criticalBadLeft alpha s ≤ x ∧
        x ≤ criticalBadRight alpha delta := by
    exact parent_bad_interval_subset_critical
      halpha hright hx

  refine ⟨u, rfl, ?_⟩
  refine ⟨q.val, hm, ?_, ?_, ?_⟩
  · dsimp [u]
    exact huval
  · rw [← hrEq]
    simpa using htrans
  · dsimp [alpha, s] at hlow hsTop hxCritical ⊢
    exact ⟨hlow, hsTop, hxCritical.1, hxCritical.2⟩

/-- Unordered two-ray version. -/
theorem transition_seed_parent_bad_has_critical_unit
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    {lam t delta L S x : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hSTop : S ≤ 1 + delta)
    (i : V)
    {j k : OtherVertex i}
    (hjk : j ≠ k)
    (hsign : raySignAt hp i j ≠ raySignAt hp i k)
    (hjArc :
      L ≤ normalizedRayTheta hp t i j ∧
      normalizedRayTheta hp t i j ≤ L + S)
    (hkArc :
      L ≤ normalizedRayTheta hp t i k ∧
      normalizedRayTheta hp t i k ≤ L + S)
    (hx :
      arcBadLeft L S ≤ x ∧
      x ≤ arcBadRight L delta) :
    ∃ u : GlobalUnitGapSlot C t,
      u.1 = i ∧
      OrdinaryCriticalUnitBadAt C t delta u x := by
  have hthetaNe :
      rayThetaAt hp i j ≠ rayThetaAt hp i k := by
    intro heq
    exact hsign
      (raySignAt_eq_of_rayThetaAt_eq
        hp hcap ht hlam i j k heq)
  rcases lt_or_gt_of_ne hthetaNe with hlt | hgt
  · exact ordered_transition_seed_parent_bad_has_critical_unit
      hp hcap C ht hlam hdeltaHalf hSTop
      i hjk hlt hsign hjArc hkArc hx
  · exact ordered_transition_seed_parent_bad_has_critical_unit
      hp hcap C ht hlam hdeltaHalf hSTop
      i hjk.symm hgt hsign.symm hkArc hjArc hx

/-- Main triangle version: every bad phase of an ordinary short triangle arc
is covered by a concrete ordinary critical q=1 transition obstruction at one
of the triangle vertices. -/
theorem triangle_parent_bad_has_ordinary_critical_unit
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    {lam t delta L S x : ℝ}
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
      normalizedEdgeTheta hp t j k hjk ≤ L + S)
    (hx :
      arcBadLeft L S ≤ x ∧
      x ≤ arcBadRight L delta) :
    ∃ u : GlobalUnitGapSlot C t,
      (u.1 = i ∨ u.1 = j ∨ u.1 = k) ∧
      OrdinaryCriticalUnitBadAt C t delta u x := by
  have hseed :=
    triangle_has_critical_transition_seed_in_ordinary_arc
      hp hcap ht hlam hij hik hjk
      hijArc hikArc hjkArc
  rcases hseed with hi | hj | hk
  · let ji : OtherVertex i := ⟨j, hij.symm⟩
    let ki : OtherVertex i := ⟨k, hik.symm⟩
    have hjiArc :
        L ≤ normalizedRayTheta hp t i ji ∧
        normalizedRayTheta hp t i ji ≤ L + S := by
      simpa [ji, normalizedEdgeTheta, normalizedRayTheta] using hijArc
    have hkiArc :
        L ≤ normalizedRayTheta hp t i ki ∧
        normalizedRayTheta hp t i ki ≤ L + S := by
      simpa [ki, normalizedEdgeTheta, normalizedRayTheta] using hikArc
    have hjki : ji ≠ ki := by
      intro h
      apply hjk
      exact congrArg Subtype.val h
    obtain ⟨u, hui, hubad⟩ :=
      transition_seed_parent_bad_has_critical_unit
        hp hcap C ht hlam hdeltaHalf hSTop
        i hjki hi.1 hjiArc hkiArc hx
    exact ⟨u, Or.inl hui, hubad⟩
  · let ijj : OtherVertex j := ⟨i, hij⟩
    let kj : OtherVertex j := ⟨k, hjk.symm⟩
    have hijRev :
        normalizedEdgeTheta hp t j i hij.symm =
          normalizedEdgeTheta hp t i j hij := by
      exact (normalizedEdgeTheta_reverse hp t hij).symm
    have hijjArc :
        L ≤ normalizedRayTheta hp t j ijj ∧
        normalizedRayTheta hp t j ijj ≤ L + S := by
      rw [← hijRev] at hijArc
      simpa [ijj, normalizedEdgeTheta, normalizedRayTheta] using hijArc
    have hkjArc :
        L ≤ normalizedRayTheta hp t j kj ∧
        normalizedRayTheta hp t j kj ≤ L + S := by
      simpa [kj, normalizedEdgeTheta, normalizedRayTheta] using hjkArc
    have hne : ijj ≠ kj := by
      intro h
      apply hik
      exact congrArg Subtype.val h
    obtain ⟨u, huj, hubad⟩ :=
      transition_seed_parent_bad_has_critical_unit
        hp hcap C ht hlam hdeltaHalf hSTop
        j hne hj.1 hijjArc hkjArc hx
    exact ⟨u, Or.inr (Or.inl huj), hubad⟩
  · let ik : OtherVertex k := ⟨i, hik⟩
    let jk : OtherVertex k := ⟨j, hjk⟩
    have hikRev :
        normalizedEdgeTheta hp t k i hik.symm =
          normalizedEdgeTheta hp t i k hik := by
      exact (normalizedEdgeTheta_reverse hp t hik).symm
    have hjkRev :
        normalizedEdgeTheta hp t k j hjk.symm =
          normalizedEdgeTheta hp t j k hjk := by
      exact (normalizedEdgeTheta_reverse hp t hjk).symm
    have hikArcK :
        L ≤ normalizedRayTheta hp t k ik ∧
        normalizedRayTheta hp t k ik ≤ L + S := by
      rw [← hikRev] at hikArc
      simpa [ik, normalizedEdgeTheta, normalizedRayTheta] using hikArc
    have hjkArcK :
        L ≤ normalizedRayTheta hp t k jk ∧
        normalizedRayTheta hp t k jk ≤ L + S := by
      rw [← hjkRev] at hjkArc
      simpa [jk, normalizedEdgeTheta, normalizedRayTheta] using hjkArc
    have hne : ik ≠ jk := by
      intro h
      apply hij
      exact congrArg Subtype.val h
    obtain ⟨u, huk, hubad⟩ :=
      transition_seed_parent_bad_has_critical_unit
        hp hcap C ht hlam hdeltaHalf hSTop
        k hne hk.1 hikArcK hjkArcK hx
    exact ⟨u, Or.inr (Or.inr huk), hubad⟩

#print axioms ordered_transition_seed_parent_bad_has_critical_unit
#print axioms transition_seed_parent_bad_has_critical_unit
#print axioms triangle_parent_bad_has_ordinary_critical_unit

end JSP000404Research
