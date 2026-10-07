import JSP000404Research.ProjectionDeficientCoreCommonWordQTTT
import JSP000404Research.ProjectionQTTTSupportOrWholeCube
import JSP000404Research.ResidualQTTTWholeCubeRecursiveOutlet
import Mathlib.Tactic

/-!
# Minimal-core Q/T/T/T support / recursion terminal

This file composes three already-separated interfaces:

* a planar deficient enlarged-candidate core reduces to standard outlets or a
  provenance-preserving Q/T/T/T state;
* the Q/T/T/T support terminal is either three support-two centres or a
  whole-cube Q/T pair;
* under inclusion-minimal Hall deficiency, a whole-cube Q/T pair re-enters
  the recursive hard-fibre alphabet.

The resulting terminal keeps the three-support branch explicit and removes the
exact-two / whole-cube branch from the geometric frontier.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

/-- A provenance-preserving Q/T/T/T state whose four second-layer centres have
at least three support-two members. -/
def CoreThreeSupportQTTTState
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {t : ℝ} {n : ℕ}
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (R : OrderedEdgeColoring (ProjectionOrdered V) (n + 1))
    (exponent : ProjectionOrdered V → ℕ)
    (T : Finset (ProjectionOrdered V)) : Prop :=
  ∃ word : Fin n → Bool,
  ∃ s x y z : ProjectionOrdered V,
  ∃ cx cy cz : Fin n,
    s ≠ x ∧ s ≠ y ∧ s ≠ z ∧
    x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    x ∈ T ∧ y ∈ T ∧ (s ∈ T ∨ z ∈ T) ∧
    s ∈ projectedLossVertices R exponent ∧
    x ∈ projectedLossVertices R exponent ∧
    y ∈ projectedLossVertices R exponent ∧
    z ∈ projectedLossVertices R exponent ∧
    exponent s = n - 2 ∧
    exponent x = n - 2 ∧
    exponent y = n - 2 ∧
    exponent z = n - 2 ∧
    cx ∈ retainedActive R x ∧
    cy ∈ retainedActive R y ∧
    cz ∈ retainedActive R z ∧
    cx ≠ cy ∧ cx ≠ cz ∧ cy ≠ cz ∧
    retainedActive R s = {cx,cy,cz} ∧
    word ∈ retainedCompletionWords R s ∧
    word ∈ translatedCompletionWords R x cx ∧
    word ∈ translatedCompletionWords R y cy ∧
    word ∈ translatedCompletionWords R z cz ∧
    ThreeSupportTwoAmongFour
      (reindexedPoint_injective hp) t C s x y z

/-- Existential wrapper for the whole-cube recursive hard-fibre alphabet. -/
def SomeQTTTRecursiveHardFibre
    {V : Type*} [LinearOrder V] {n : ℕ}
    (R : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Prop :=
  ∃ source : V,
  ∃ owner alt₁ alt₂ : Fin n,
    QTTTWholeCubeRecursiveHardFibre
      R exponent source owner alt₁ alt₂

theorem planar_coreQTTT_threeSupport_or_recursive
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    {T : Finset (ProjectionOrdered V)}
    (hdef :
      BlockDeficient
        (fun i => 2 ^ centreExponent (C i) t)
        (planarEnlargedCandidateBlock
          hp hcap (by omega : 1 ≤ n)
          hdelta0 hdeltaHalf ht hlam C)
        T)
    (hmin :
      ∀ U : Finset (ProjectionOrdered V),
        U ⊂ T →
        ¬ BlockDeficient
          (fun i => 2 ^ centreExponent (C i) t)
          (planarEnlargedCandidateBlock
            hp hcap (by omega : 1 ≤ n)
            hdelta0 hdeltaHalf ht hlam C)
          U)
    (hQ :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      let exponent := planarCentreExponent hp C
      CoreQTTTState R exponent T) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let R :=
      planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
    let exponent := planarCentreExponent hp C
    CoreThreeSupportQTTTState hp C R exponent T
    ∨
    (∃ hole : Fin n → Bool,
      hole ∉ coveredCompletionWords R)
    ∨
    (∃ blocker : ProjectionOrdered V,
      1 ≤ dyadicProfileSurplus
        exponent (projectedFree R) blocker)
    ∨
    SomeQTTTRecursiveHardFibre R exponent := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let hn1 : 1 ≤ n := by omega
  let hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp C

  have hQ' : CoreQTTTState R exponent T := by
    simpa [R,exponent,hn1,hdelta1] using hQ

  have hprofile :=
    genericProjection_lowerBranch_profile_hypotheses
      hp hcap hn1 hdelta0 hdelta1 ht hlam C
  have hexp :
      ∀ q : ProjectionOrdered V, exponent q ≤ n := by
    intro q
    exact Nat.le_of_lt
      (by simpa [exponent] using hprofile.1 q)
  have honeLoss :
      ∀ q : ProjectionOrdered V,
        (active R q).card ≤ n - exponent q + 1 := by
    intro q
    simpa [R,exponent] using hprofile.2 q
  have hdefR :
      BlockDeficient
        (fun q => 2 ^ exponent q)
        (enlargedProjectedCandidateBlock R exponent)
        T := by
    simpa [planarEnlargedCandidateBlock,R,exponent,
      planarCentreExponent,hn1,hdelta1] using hdef
  have hminR :
      ∀ U : Finset (ProjectionOrdered V),
        U ⊂ T →
        ¬ BlockDeficient
          (fun q => 2 ^ exponent q)
          (enlargedProjectedCandidateBlock R exponent)
          U := by
    intro U hUT
    simpa [planarEnlargedCandidateBlock,R,exponent,
      planarCentreExponent,hn1,hdelta1] using hmin U hUT

  obtain ⟨word,s,x,y,z,cx,cy,cz,
      hsx,hsy,hsz,hxy,hxz,hyz,
      hxCore,hyCore,hthirdCore,
      hsLoss,hxLoss,hyLoss,hzLoss,
      hsSecond,hxSecond,hySecond,hzSecond,
      hcx,hcy,hcz,hcxy,hcxz,hcyz,
      hsActive,hsQ,hxT,hyT,hzT⟩ := hQ'

  have hterm :=
    planar_QTTT_threeSupport_or_wholeCube
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam C
      hsx hsy hsz hxy hxz hyz
      (by simpa [R,exponent,hn1,hdelta1,
          planarCentreExponent] using hsLoss)
      (by simpa [R,exponent,hn1,hdelta1,
          planarCentreExponent] using hxLoss)
      (by simpa [R,exponent,hn1,hdelta1,
          planarCentreExponent] using hyLoss)
      (by simpa [R,exponent,hn1,hdelta1,
          planarCentreExponent] using hzLoss)
      (by simpa [exponent,planarCentreExponent] using hsSecond)
      (by simpa [exponent,planarCentreExponent] using hxSecond)
      (by simpa [exponent,planarCentreExponent] using hySecond)
      (by simpa [exponent,planarCentreExponent] using hzSecond)
      (by simpa [R] using hcx)
      (by simpa [R] using hcy)
      (by simpa [R] using hcz)
      hcxy hcxz hcyz
      (by simpa [R] using hsActive)
      (by simpa [R] using hsQ)
      (by simpa [R] using hxT)
      (by simpa [R] using hyT)
      (by simpa [R] using hzT)

  rcases hterm with hthree | hwhole
  · exact Or.inl
      ⟨word,s,x,y,z,cx,cy,cz,
        hsx,hsy,hsz,hxy,hxz,hyz,
        hxCore,hyCore,hthirdCore,
        hsLoss,hxLoss,hyLoss,hzLoss,
        hsSecond,hxSecond,hySecond,hzSecond,
        hcx,hcy,hcz,hcxy,hcxz,hcyz,
        hsActive,hsQ,hxT,hyT,hzT,hthree⟩

  · have hout :=
      QTTT_wholeCube_hole_or_paid_or_recursive_fibre
        R exponent hexp honeLoss hn3
        hdefR hminR
        hsx hsy hsz
        hxCore hyCore hthirdCore
        hsLoss hxLoss hyLoss hzLoss
        hsSecond hxSecond hySecond hzSecond
        hcx hcy hcz hsActive hwhole
    rcases hout with hhole | hpaid | hxRec | hyRec | hzRec | hsRec
    · exact Or.inr (Or.inl hhole)
    · exact Or.inr (Or.inr (Or.inl hpaid))
    · exact Or.inr (Or.inr (Or.inr
        ⟨x,cx,cy,cz,hxRec⟩))
    · exact Or.inr (Or.inr (Or.inr
        ⟨y,cy,cx,cz,hyRec⟩))
    · exact Or.inr (Or.inr (Or.inr
        ⟨z,cz,cx,cy,hzRec⟩))
    · exact Or.inr (Or.inr (Or.inr
        ⟨s,cz,cx,cy,hsRec⟩))

#print axioms planar_coreQTTT_threeSupport_or_recursive

end ProjectionOrdered
end JSP000404Research
