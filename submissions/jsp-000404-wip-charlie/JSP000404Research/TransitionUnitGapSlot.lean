import JSP000404Research.CentreTransitionRefinement
import JSP000404Research.CriticalUnitQuotient
import JSP000404Research.SixPointUnitGapSlots
import JSP000404Research.CentreAdjacentTransitionOccurrence
import Mathlib.Tactic

/-!
# Concrete unit-gap slots carried by ordinary sign transitions

A critical terminal obstruction must not merely have quotient value one; its
specific gap coordinate must be carried by an adjacent sign transition.

This file packages that positional certificate and proves a reusable
refinement theorem:

if two rays at one centre have opposite canonical signs and normalized
projective separation at most 1+delta, then some nested adjacent transition
gap has width in [1,1+delta], hence quotient exactly one, and therefore defines
a concrete CentreUnitGap / GlobalUnitGapSlot transition slot.
-/

namespace JSP000404Research

/-- A local q=1 slot whose coordinate is an ordinary adjacent sign-changing
ray gap. -/
def CentreUnitGapOrdinaryTransition
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : CentreUnitGap C t) : Prop :=
  ∃ m : ℕ, ∃ hm : m + 1 < C.rays.length,
    u.1.val = m ∧
    Nat.floor
      (t * ((rayThetaAt hp i
          (C.rays.get ⟨m + 1, hm⟩) -
        rayThetaAt hp i
          (C.rays.get ⟨m, by omega⟩)) / Real.pi)) = 1 ∧
    raySignAt hp i
        (C.rays.get ⟨m, by omega⟩) ≠
      raySignAt hp i
        (C.rays.get ⟨m + 1, hm⟩)

/-- Global sigma-slot version. -/
def GlobalUnitGapOrdinaryTransition
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : GlobalUnitGapSlot C t) : Prop :=
  CentreUnitGapOrdinaryTransition (C u.1) t u.2

/-- Bridge from an adjacent ray index and floor-one equation to the dependent
CentreUnitGap subtype. -/
theorem exists_centreUnitGap_of_adjacent_floor_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (m : ℕ)
    (hm : m + 1 < C.rays.length)
    (hfloor :
      Nat.floor
        (t * ((rayThetaAt hp i
            (C.rays.get ⟨m + 1, hm⟩) -
          rayThetaAt hp i
            (C.rays.get ⟨m, by omega⟩)) / Real.pi)) = 1) :
    ∃ u : CentreUnitGap C t,
      u.1.val = m := by
  have hmA : m + 1 < C.angles.length := by
    simpa [C.angles_length] using hm
  have hqList :
      (quotientList t C.gaps)[m] = 1 := by
    rw [centre_adjacent_quotient_getElem_eq C t m hmA]
    simpa [CentreProjectiveCycle.angles] using hfloor
  have hmGap : m < C.gaps.length := by
    rw [C.gaps_length]
    omega
  let rGap : Fin C.gaps.length := ⟨m, hmGap⟩
  let rList : Fin (quotientList t C.gaps).length :=
    ⟨m, by
      rw [quotientList_length]
      exact hmGap⟩
  have hbridge :
      centreQuotient C t rGap =
        (quotientList t C.gaps).get rList := by
    simp [centreQuotient, quotientList, rGap, rList]
  have hlistGet :
      (quotientList t C.gaps).get rList = 1 := by
    simpa [rList] using hqList
  have hunit : centreQuotient C t rGap = 1 := by
    rw [hbridge, hlistGet]
  exact ⟨⟨rGap, hunit⟩, rfl⟩

/-- Transition-pair refinement to a concrete local q=1 slot. -/
theorem exists_unit_ordinary_transition_slot_between_rays
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    {j k : OtherVertex i}
    (hjk : j ≠ k)
    (hsign : raySignAt hp i j ≠ raySignAt hp i k)
    (hwidth :
      t * (|rayThetaAt hp i j - rayThetaAt hp i k| /
        Real.pi) ≤ 1 + delta) :
    ∃ u : CentreUnitGap C t,
      CentreUnitGapOrdinaryTransition C t u := by
  have hthetaNe :
      rayThetaAt hp i j ≠ rayThetaAt hp i k := by
    intro heq
    have hsignEq :=
      raySignAt_eq_of_rayThetaAt_eq
        hp hcap ht hlam i j k heq
    exact hsign hsignEq
  rcases lt_or_gt_of_ne hthetaNe with htheta | htheta
  · obtain ⟨q, r, hsucc, _hjQ, _hrK,
        htrans, hlow, hleSeed⟩ :=
      C.exists_adjacent_transition_inside_ordered_seed
        hcap ht hlam htheta hsign
    let s : ℝ :=
      t * ((rayThetaAt hp i (C.rays.get r) -
        rayThetaAt hp i (C.rays.get q)) / Real.pi)
    have hsTop : s ≤ 1 + delta := by
      have habs :
          |rayThetaAt hp i j - rayThetaAt hp i k| =
            rayThetaAt hp i k - rayThetaAt hp i j := by
        rw [abs_of_nonpos (sub_nonpos.mpr htheta.le)]
        ring
      have hseedTop :
          t * ((rayThetaAt hp i k -
            rayThetaAt hp i j) / Real.pi) ≤ 1 + delta := by
        simpa [habs] using hwidth
      exact hleSeed.trans hseedTop
    have hfloorS : Nat.floor s = 1 :=
      critical_gap_floor_eq_one hdeltaHalf hlow hsTop
    have hm : q.val + 1 < C.rays.length := by
      rw [← hsucc]
      exact r.isLt
    have hrEq :
        r = ⟨q.val + 1, hm⟩ := by
      apply Fin.ext
      exact hsucc
    have hfloor :
        Nat.floor
          (t * ((rayThetaAt hp i
              (C.rays.get ⟨q.val + 1, hm⟩) -
            rayThetaAt hp i
              (C.rays.get ⟨q.val, q.isLt⟩)) / Real.pi)) = 1 := by
      rw [← hrEq]
      exact hfloorS
    obtain ⟨u, huval⟩ :=
      exists_centreUnitGap_of_adjacent_floor_one
        C t q.val hm hfloor
    refine ⟨u, q.val, hm, huval, hfloor, ?_⟩
    rw [← hrEq]
    simpa using htrans
  · obtain ⟨q, r, hsucc, _hkQ, _hrJ,
        htrans, hlow, hleSeed⟩ :=
      C.exists_adjacent_transition_inside_ordered_seed
        hcap ht hlam htheta hsign.symm
    let s : ℝ :=
      t * ((rayThetaAt hp i (C.rays.get r) -
        rayThetaAt hp i (C.rays.get q)) / Real.pi)
    have hsTop : s ≤ 1 + delta := by
      have habs :
          |rayThetaAt hp i j - rayThetaAt hp i k| =
            rayThetaAt hp i j - rayThetaAt hp i k := by
        rw [abs_of_nonneg (sub_nonneg.mpr htheta.le)]
      have hseedTop :
          t * ((rayThetaAt hp i j -
            rayThetaAt hp i k) / Real.pi) ≤ 1 + delta := by
        simpa [habs] using hwidth
      exact hleSeed.trans hseedTop
    have hfloorS : Nat.floor s = 1 :=
      critical_gap_floor_eq_one hdeltaHalf hlow hsTop
    have hm : q.val + 1 < C.rays.length := by
      rw [← hsucc]
      exact r.isLt
    have hrEq :
        r = ⟨q.val + 1, hm⟩ := by
      apply Fin.ext
      exact hsucc
    have hfloor :
        Nat.floor
          (t * ((rayThetaAt hp i
              (C.rays.get ⟨q.val + 1, hm⟩) -
            rayThetaAt hp i
              (C.rays.get ⟨q.val, q.isLt⟩)) / Real.pi)) = 1 := by
      rw [← hrEq]
      exact hfloorS
    obtain ⟨u, huval⟩ :=
      exists_centreUnitGap_of_adjacent_floor_one
        C t q.val hm hfloor
    refine ⟨u, q.val, hm, huval, hfloor, ?_⟩
    rw [← hrEq]
    simpa using htrans

/-- Family/global version. -/
theorem exists_global_unit_ordinary_transition_slot_between_rays
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (i : V)
    {j k : OtherVertex i}
    (hjk : j ≠ k)
    (hsign : raySignAt hp i j ≠ raySignAt hp i k)
    (hwidth :
      t * (|rayThetaAt hp i j - rayThetaAt hp i k| /
        Real.pi) ≤ 1 + delta) :
    ∃ u : GlobalUnitGapSlot C t,
      u.1 = i ∧
      GlobalUnitGapOrdinaryTransition C t u := by
  obtain ⟨u, hu⟩ :=
    exists_unit_ordinary_transition_slot_between_rays
      (C i) hcap ht hlam hdeltaHalf
      hjk hsign hwidth
  exact ⟨⟨i, u⟩, rfl, hu⟩

#print axioms exists_centreUnitGap_of_adjacent_floor_one
#print axioms exists_unit_ordinary_transition_slot_between_rays
#print axioms exists_global_unit_ordinary_transition_slot_between_rays

end JSP000404Research
