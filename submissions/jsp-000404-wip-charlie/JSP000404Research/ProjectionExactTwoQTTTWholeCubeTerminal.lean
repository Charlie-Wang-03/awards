import JSP000404Research.ProjectionExactTwoQTTTPaletteTransfer
import JSP000404Research.ResidualQTTTConsecutivePaletteTerminal
import Mathlib.Tactic

/-!
# Planar exact-two Q/T/T/T whole-cube terminal

This file composes the exact-two support-role palette transfer with the generic
consecutive-palette Q/T/T/T theorem.

Thus the planar exact-two support terminal no longer ends at consecutive
palettes / common colours / skinny triangles: it forces one translated owner
to have the same retained palette as the completion owner and its entire
translated completion slice to equal the completion owner's retained cube.
-/

namespace JSP000404Research
namespace ProjectionOrdered

theorem planar_exactTwo_QTTT_force_whole_cube_QT_pair
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
    {s x y z o₁ o₂ u₁ u₂ : ProjectionOrdered V}
    (hsx : s ≠ x) (hsy : s ≠ y) (hsz : s ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ho12 : o₁ ≠ o₂)
    (ho1u1 : o₁ ≠ u₁) (ho1u2 : o₁ ≠ u₂)
    (ho2u1 : o₂ ≠ u₁) (ho2u2 : o₂ ≠ u₂)
    (hu12 : u₁ ≠ u₂)
    (ho1Mem : o₁ ∈ ({s,x,y,z} : Finset (ProjectionOrdered V)))
    (ho2Mem : o₂ ∈ ({s,x,y,z} : Finset (ProjectionOrdered V)))
    (hu1Mem : u₁ ∈ ({s,x,y,z} : Finset (ProjectionOrdered V)))
    (hu2Mem : u₂ ∈ ({s,x,y,z} : Finset (ProjectionOrdered V)))
    (hsLoss :
      s ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp C))
    (hxLoss :
      x ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp C))
    (hyLoss :
      y ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp C))
    (hzLoss :
      z ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp C))
    (hsSecond : centreExponent (C s) t = n - 2)
    (hxSecond : centreExponent (C x) t = n - 2)
    (hySecond : centreExponent (C y) t = n - 2)
    (hzSecond : centreExponent (C z) t = n - 2)
    (ho1Support :
      positiveSupport (centreQuotient (C o₁) t) = 1)
    (ho2Support :
      positiveSupport (centreQuotient (C o₂) t) = 1)
    (hu1Support :
      positiveSupport (centreQuotient (C u₁) t) = 2)
    (hu2Support :
      positiveSupport (centreQuotient (C u₂) t) = 2)
    (cert₁ :
      HighExponentTransitionIntervalCertificate
        (reindexedPoint_injective hp) t u₁ (C u₁))
    (cert₂ :
      HighExponentTransitionIntervalCertificate
        (reindexedPoint_injective hp) t u₂ (C u₂))
    (hqe1 : cert₁.qe = 1)
    (hqe2 : cert₂.qe = 1)
    {word : Fin n → Bool}
    {cx cy cz : Fin n}
    (hcx :
      cx ∈ retainedActive
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam) x)
    (hcy :
      cy ∈ retainedActive
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam) y)
    (hcz :
      cz ∈ retainedActive
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam) z)
    (hcxy : cx ≠ cy) (hcxz : cx ≠ cz) (hcyz : cy ≠ cz)
    (hsActive :
      retainedActive
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam) s
        = {cx,cy,cz})
    (hsQ :
      word ∈ retainedCompletionWords
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam) s)
    (hxT :
      word ∈ translatedCompletionWords
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam) x cx)
    (hyT :
      word ∈ translatedCompletionWords
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam) y cy)
    (hzT :
      word ∈ translatedCompletionWords
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam) z cz) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let R :=
      planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
    (
      retainedActive R x = retainedActive R s ∧
      translatedCompletionWords R x cx =
        retainedCompletionWords R s
    )
    ∨
    (
      retainedActive R y = retainedActive R s ∧
      translatedCompletionWords R y cy =
        retainedCompletionWords R s
    )
    ∨
    (
      retainedActive R z = retainedActive R s ∧
      translatedCompletionWords R z cz =
        retainedCompletionWords R s
    ) := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let R :=
    planarStandardResidualColoring
      hp hcap (by omega : 1 ≤ n)
      hdelta0 (by linarith : delta < 1) ht hlam
  let exponent := planarCentreExponent hp C

  obtain ⟨ms,mx,my,mz,hps,hpx,hpy,hpz⟩ :=
    exactTwo_QTTT_palettes_consecutive_by_role_transfer
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam C
      hsx hsy hsz hxy hxz hyz
      ho12 ho1u1 ho1u2 ho2u1 ho2u2 hu12
      ho1Mem ho2Mem hu1Mem hu2Mem
      hsLoss hxLoss hyLoss hzLoss
      hsSecond hxSecond hySecond hzSecond
      ho1Support ho2Support hu1Support hu2Support
      cert₁ cert₂ hqe1 hqe2

  have hprofile :=
    genericProjection_lowerBranch_profile_hypotheses
      hp hcap (by omega : 1 ≤ n)
      hdelta0 (by linarith : delta < 1) ht hlam C
  have hexp : ∀ q, exponent q ≤ n := by
    intro q
    exact Nat.le_of_lt
      (by simpa [exponent] using hprofile.1 q)
  have hone :
      ∀ q, (active R q).card ≤ n - exponent q + 1 := by
    intro q
    simpa [R,exponent] using hprofile.2 q

  have hsLoss' :
      s ∈ projectedLossVertices R exponent := by
    simpa [R,exponent] using hsLoss
  have hxLoss' :
      x ∈ projectedLossVertices R exponent := by
    simpa [R,exponent] using hxLoss
  have hyLoss' :
      y ∈ projectedLossVertices R exponent := by
    simpa [R,exponent] using hyLoss
  have hzLoss' :
      z ∈ projectedLossVertices R exponent := by
    simpa [R,exponent] using hzLoss

  have hsSecond' : exponent s = n - 2 := by
    simpa [exponent,planarCentreExponent] using hsSecond
  have hxSecond' : exponent x = n - 2 := by
    simpa [exponent,planarCentreExponent] using hxSecond
  have hySecond' : exponent y = n - 2 := by
    simpa [exponent,planarCentreExponent] using hySecond
  have hzSecond' : exponent z = n - 2 := by
    simpa [exponent,planarCentreExponent] using hzSecond

  exact
    OrderedEdgeColoring.QTTT_consecutive_palettes_force_whole_cube_QT_pair
      R exponent hexp hone
      hsx hsy hsz hxy hxz hyz
      hsLoss' hxLoss' hyLoss' hzLoss'
      hsSecond' hxSecond' hySecond' hzSecond'
      (by simpa [R] using hcx)
      (by simpa [R] using hcy)
      (by simpa [R] using hcz)
      hcxy hcxz hcyz
      (by simpa [R] using hsActive)
      (by simpa [R] using hsQ)
      (by simpa [R] using hxT)
      (by simpa [R] using hyT)
      (by simpa [R] using hzT)
      hps hpx hpy hpz

#print axioms planar_exactTwo_QTTT_force_whole_cube_QT_pair

end ProjectionOrdered
end JSP000404Research
