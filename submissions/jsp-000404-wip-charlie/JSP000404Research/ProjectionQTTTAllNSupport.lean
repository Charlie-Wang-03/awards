import JSP000404Research.ProjectionEnlargedCandidateHall
import JSP000404Research.SecondLayerFourSupportReduction
import JSP000404Research.ResidualSecondLayerFinThreeDeficiency
import Mathlib.Tactic

/-!
# Uniform Q/T/T/T support reduction for all n >= 3

The previous planar Q/T/T/T root left an n=3 exception.  Four-centre
transition packing removes that exception: among any four distinct
second-layer centres, at least two have quotient support two for every n>=3.

This file exposes the uniform planar terminal used by the next geometry step.
-/

namespace JSP000404Research

theorem planar_QTTT_secondLayer_has_two_supportTwo
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
    {s x y z : ProjectionOrdered V}
    (hsx : s ≠ x) (hsy : s ≠ y) (hsz : s ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hsSecond : centreExponent (C s) t = n - 2)
    (hxSecond : centreExponent (C x) t = n - 2)
    (hySecond : centreExponent (C y) t = n - 2)
    (hzSecond : centreExponent (C z) t = n - 2) :
    ∃ a b : ProjectionOrdered V,
      a ≠ b ∧
      a ∈ ({s,x,y,z} : Finset (ProjectionOrdered V)) ∧
      b ∈ ({s,x,y,z} : Finset (ProjectionOrdered V)) ∧
      positiveSupport (centreQuotient (C a) t) = 2 ∧
      positiveSupport (centreQuotient (C b) t) = 2 := by
  have hcapR :
      AngleCap (reindexedPoint p) lam := by
    intro a b c hab hac hbc
    apply hcap a.toOriginal b.toOriginal c.toOriginal
    · intro h
      apply hab
      exact ProjectionOrdered.toOriginal_injective h
    · intro h
      apply hac
      exact ProjectionOrdered.toOriginal_injective h
    · intro h
      apply hbc
      exact ProjectionOrdered.toOriginal_injective h
  exact four_secondLayer_has_two_supportTwo_of_three_le_n
    (p := reindexedPoint p)
    (reindexedPoint_injective hp)
    hcapR
    hn3 hdelta0 hdeltaHalf ht hlam
    C
    hsx hsy hsz hxy hxz hyz
    hsSecond hxSecond hySecond hzSecond

/-- Uniform current planar root: every non-closed obstruction is a saturated
Q/T/T/T state on four second-layer loss centres, and two of those four
centres are support-two. -/
theorem planar_deficientCore_girthFree_QTTT_twoSupport_root
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hcard : 3 ≤ Fintype.card (ProjectionOrdered V))
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
        T) :
    let R :=
      planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
    let exponent := planarCentreExponent hp C
    (
      ∃ hole : Fin n → Bool,
        hole ∉ coveredCompletionWords R
    )
    ∨
    (
      ∃ q : ProjectionOrdered V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree R) q
    )
    ∨
    (
      ∃ q : ProjectionOrdered V,
        ExactProjectedBudget R exponent q
    )
    ∨
    (
      ∃ source : ProjectionOrdered V,
        ExactRecursiveOutlet R exponent source
    )
    ∨
    (
      ∃ q : ProjectionOrdered V,
        q ∈ projectedLossVertices R exponent ∧
        exponent q + 3 ≤ n
    )
    ∨
    (
      ∃ word : Fin n → Bool,
      ∃ s x y z : ProjectionOrdered V,
      ∃ cx cy cz : Fin n,
        s ≠ x ∧ s ≠ y ∧ s ≠ z ∧
        x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
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
        (
          ∃ a b : ProjectionOrdered V,
            a ≠ b ∧
            a ∈ ({s,x,y,z} :
              Finset (ProjectionOrdered V)) ∧
            b ∈ ({s,x,y,z} :
              Finset (ProjectionOrdered V)) ∧
            positiveSupport (centreQuotient (C a) t) = 2 ∧
            positiveSupport (centreQuotient (C b) t) = 2
        )
    ) := by
  let hn1 : 1 ≤ n := by omega
  let hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp C
  rcases
    planar_deficientCore_girthFree_QTTT_support_root
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      hcard C hdef
    with hhole | hpaid | hexact | hrec | hdeep | hQTTT
  · exact Or.inl hhole
  · exact Or.inr (Or.inl hpaid)
  · exact Or.inr (Or.inr (Or.inl hexact))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hrec)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep))))
  · obtain ⟨word,s,x,y,z,cx,cy,cz,
      hsx,hsy,hsz,hxy,hxz,hyz,
      hsLoss,hxLoss,hyLoss,hzLoss,
      hsSecond,hxSecond,hySecond,hzSecond,
      hcx,hcy,hcz,
      hcxy,hcxz,hcyz,hsActive,
      hsQ,hxT,hyT,hzT,_holdSupport⟩ := hQTTT
    have hsSecondGeom :
        centreExponent (C s) t = n - 2 := by
      simpa [exponent,planarCentreExponent] using hsSecond
    have hxSecondGeom :
        centreExponent (C x) t = n - 2 := by
      simpa [exponent,planarCentreExponent] using hxSecond
    have hySecondGeom :
        centreExponent (C y) t = n - 2 := by
      simpa [exponent,planarCentreExponent] using hySecond
    have hzSecondGeom :
        centreExponent (C z) t = n - 2 := by
      simpa [exponent,planarCentreExponent] using hzSecond
    have hsupport :=
      planar_QTTT_secondLayer_has_two_supportTwo
        hp hcap hn3 hdelta0 hdeltaHalf ht hlam C
        hsx hsy hsz hxy hxz hyz
        hsSecondGeom hxSecondGeom hySecondGeom hzSecondGeom
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨word,s,x,y,z,cx,cy,cz,
        hsx,hsy,hsz,hxy,hxz,hyz,
        hsLoss,hxLoss,hyLoss,hzLoss,
        hsSecond,hxSecond,hySecond,hzSecond,
        hcx,hcy,hcz,
        hcxy,hcxz,hcyz,hsActive,
        hsQ,hxT,hyT,hzT,hsupport⟩))))

#print axioms planar_QTTT_secondLayer_has_two_supportTwo
#print axioms planar_deficientCore_girthFree_QTTT_twoSupport_root

end JSP000404Research
