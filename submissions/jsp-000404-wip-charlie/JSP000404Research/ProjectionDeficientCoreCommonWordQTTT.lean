import JSP000404Research.ResidualDeficientCoreSecondLayerOutlet
import JSP000404Research.ResidualSecondLayerQTTTCoreThreeMembership
import JSP000404Research.ProjectionTopSecondLossClosure
import Mathlib.Tactic

/-!
# Planar deficient core to a provenance-preserving Q/T/T/T state

The common-word deficient-core reduction now keeps three pairwise-distinct
second-layer carriers.  In the planar lower branch this is enough to connect
the Hall root to the source-preserving Q/T/T/T canonicalization.

Every other branch is discharged into the existing standard outlet alphabet:
a Boolean hole, strict profile surplus, exact projected budget, exact recursive
outlet, or deep projected loss.  Top and top--second branches are closed by
the planar multiplicity lemmas before they can survive as structural terminals.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- The four-centre state produced by the common-word second-layer
canonicalization, with enough minimal-core provenance for the later Hall
augmentation arguments. -/
def CoreQTTTState
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (R : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V) : Prop :=
  ∃ word : Fin n → Bool,
  ∃ s x y z : V,
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
    word ∈ translatedCompletionWords R z cz

theorem planar_deficientCore_standard_or_coreQTTT
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
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let R :=
      planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
    let exponent := planarCentreExponent hp C
    (
      (∃ hole : Fin n → Bool,
        hole ∉ coveredCompletionWords R)
      ∨
      (∃ q : ProjectionOrdered V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree R) q)
      ∨
      (∃ q : ProjectionOrdered V,
        ExactProjectedBudget R exponent q)
      ∨
      (∃ source : ProjectionOrdered V,
        ExactRecursiveOutlet R exponent source)
      ∨
      (∃ q : ProjectionOrdered V,
        q ∈ projectedLossVertices R exponent ∧
        exponent q + 3 ≤ n)
      ∨
      CoreQTTTState R exponent T
    ) := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let hn1 : 1 ≤ n := by omega
  let hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp C

  have hexpLt :
      ∀ q : ProjectionOrdered V, exponent q < n :=
    planarCentreExponent_lt_n
      hp hn1 hdelta0 hdelta1 ht C
  have hexp :
      ∀ q : ProjectionOrdered V, exponent q ≤ n := by
    intro q
    exact Nat.le_of_lt (hexpLt q)
  have honeLoss :
      ∀ q, (active R q).card ≤ n - exponent q + 1 :=
    planarStandardResidual_oneLayer_budget
      hp hcap hn1 hdelta0 hdelta1 ht hlam C
  have htop :
      ((Finset.univ : Finset (ProjectionOrdered V)).filter
        (fun q => exponent q = n - 1)).card ≤ 1 := by
    simpa [exponent,planarCentreExponent] using
      (projectionOrdered_topExponent_filter_card_le_one
        hp hcap hcard (by omega : 2 ≤ n)
        hdelta0 hdeltaHalf ht hlam C)
  have hdefR :
      BlockDeficient
        (fun q => 2 ^ exponent q)
        (enlargedProjectedCandidateBlock R exponent)
        T := by
    simpa [planarEnlargedCandidateBlock,R,exponent,
      planarCentreExponent,hn1,hdelta1] using hdef

  have closeTop
      {q : ProjectionOrdered V}
      (hqLoss : q ∈ projectedLossVertices R exponent)
      (hqTop : exponent q = n - 1) :
      (∃ hole : Fin n → Bool,
        hole ∉ coveredCompletionWords R)
      ∨
      (∃ z : ProjectionOrdered V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree R) z)
      ∨
      (∃ z : ProjectionOrdered V,
        ExactProjectedBudget R exponent z)
      ∨
      (∃ z : ProjectionOrdered V,
        z ∈ projectedLossVertices R exponent ∧
        exponent z + 3 ≤ n) := by
    have hqLossGeom :
        q ∈ projectedLossVertices
          (planarStandardResidualColoring
            hp hcap (by omega : 1 ≤ n)
            hdelta0 (by linarith : delta < 1) ht hlam)
          (planarCentreExponent hp C) := by
      simpa [R,exponent,hn1,hdelta1] using hqLoss
    have hqTopGeom :
        centreExponent (C q) t = n - 1 := by
      simpa [exponent,planarCentreExponent] using hqTop
    simpa [R,exponent,hn1,hdelta1,planarCentreExponent] using
      (planar_topLoss_closed_outlet
        hp hcap hn3 hdelta0 hdeltaHalf ht hlam
        hcard C hqLossGeom hqTopGeom)

  rcases
    deficientCore_secondLayer_commonWord_or_recursiveOverload
      R exponent hexpLt hexp honeLoss htop hdefR
    with hcommon | hexactShared | htopShared

  · obtain ⟨word,u,v,w,huv,huw,hvw,hout⟩ := hcommon
    cases hout with
    | paid q hq =>
        exact Or.inr (Or.inl ⟨q,hq⟩)
    | exactRecursive source hout =>
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨source,hout⟩)))
    | exact q hq =>
        exact Or.inr (Or.inr (Or.inl ⟨q,hq⟩))
    | deep q hqLoss hqDeep =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨q,hqLoss,hqDeep⟩))))
    | topSecond top second hne htopLoss hsecondLoss
        htopExp hsecondExp htopWord hsecondWord =>
        have htopExpGeom :
            centreExponent (C top.1) t = n - 1 := by
          simpa [exponent,planarCentreExponent] using htopExp
        have hsecondExpGeom :
            centreExponent (C second.1) t = n - 2 := by
          simpa [exponent,planarCentreExponent] using hsecondExp
        have hsecondLossGeom :
            second.1 ∈ projectedLossVertices
              (planarStandardResidualColoring
                hp hcap (by omega : 1 ≤ n)
                hdelta0 (by linarith : delta < 1) ht hlam)
              (planarCentreExponent hp C) := by
          simpa [R,exponent,hn1,hdelta1] using hsecondLoss
        rcases
          planar_topSecond_loss_pair_standard_outlet
            hp hcap hn3 hdelta0 hdeltaHalf ht hlam
            hcard C htopExpGeom hsecondExpGeom hsecondLossGeom
          with hhole | hpaid | hexact | hdeep
        · exact Or.inl hhole
        · exact Or.inr (Or.inl hpaid)
        · exact Or.inr (Or.inr (Or.inl hexact))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep))))
    | threeSecond huLoss hvLoss hwLoss
        huSecond hvSecond hwSecond huWord hvWord hwWord =>
        rcases
          core_threeSecond_commonWord_QTTT_or_closed_three_core_members
            R exponent hexpLt hexp honeLoss
            huv huw hvw
            huLoss hvLoss hwLoss
            huSecond hvSecond hwSecond
            huWord hvWord hwWord
          with hhole | hpaid | hexact | htopLoss | hdeep | hQTTT
        · exact Or.inl hhole
        · exact Or.inr (Or.inl hpaid)
        · exact Or.inr (Or.inr (Or.inl hexact))
        · obtain ⟨q,hqLoss,hqTop⟩ := htopLoss
          rcases closeTop hqLoss hqTop
            with hhole2 | hpaid2 | hexact2 | hdeep2
          · exact Or.inl hhole2
          · exact Or.inr (Or.inl hpaid2)
          · exact Or.inr (Or.inr (Or.inl hexact2))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep2))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep))))
        · obtain ⟨s,x,y,z,cx,cy,cz,
            hsx,hsy,hsz,hxy,hxz,hyz,
            hxCore,hyCore,hthirdCore,
            hsLoss,hxLoss,hyLoss,hzLoss,
            hsSecond,hxSecond,hySecond,hzSecond,
            hcx,hcy,hcz,hcxy,hcxz,hcyz,
            hsActive,hsQ,hxT,hyT,hzT⟩ := hQTTT
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨word,s,x,y,z,cx,cy,cz,
              hsx,hsy,hsz,hxy,hxz,hyz,
              hxCore,hyCore,hthirdCore,
              hsLoss,hxLoss,hyLoss,hzLoss,
              hsSecond,hxSecond,hySecond,hzSecond,
              hcx,hcy,hcz,hcxy,hcxz,hcyz,
              hsActive,hsQ,hxT,hyT,hzT⟩))))

  · obtain ⟨q,_hqT,hqExact,_hqShared⟩ := hexactShared
    exact Or.inr (Or.inr (Or.inl ⟨q,hqExact⟩))

  · obtain ⟨q,_hqT,hqLoss,hqTop,_hqShared⟩ := htopShared
    rcases closeTop hqLoss hqTop
      with hhole | hpaid | hexact | hdeep
    · exact Or.inl hhole
    · exact Or.inr (Or.inl hpaid)
    · exact Or.inr (Or.inr (Or.inl hexact))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep))))

#print axioms planar_deficientCore_standard_or_coreQTTT

end ProjectionOrdered
end JSP000404Research
