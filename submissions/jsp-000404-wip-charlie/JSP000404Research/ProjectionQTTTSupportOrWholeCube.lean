import JSP000404Research.ProjectionQTTTSupportTerminal
import JSP000404Research.ProjectionExactTwoQTTTWholeCubeTerminal
import Mathlib.Tactic

/-!
# Planar Q/T/T/T support-or-whole-cube terminal

A saturated planar Q/T/T/T state on four second-layer projected-loss centres
has only two possibilities:

* at least three of the four centres are support-two; or
* the exact-two support branch occurs, in which case the two support-one /
  two support-two role decomposition forces all four retained palettes to be
  consecutive and therefore upgrades one translated owner to a whole-cube
  Q/T partner of the completion owner.

This packages the support terminal in the form needed by the enlarged-Hall
assembly.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

theorem planar_QTTT_threeSupport_or_wholeCube
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
    {s x y z : ProjectionOrdered V}
    (hsx : s ≠ x) (hsy : s ≠ y) (hsz : s ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
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
    ThreeSupportTwoAmongFour
      (reindexedPoint_injective hp) t C s x y z
    ∨
    (
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R s x cx ∨
      WholeCubeQTPair R s y cy ∨
      WholeCubeQTPair R s z cz
    ) := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let R :=
    planarStandardResidualColoring
      hp hcap (by omega : 1 ≤ n)
      hdelta0 (by linarith : delta < 1) ht hlam

  have hterm :=
    planar_QTTT_four_secondLayer_support_terminal
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam C
      hsx hsy hsz hxy hxz hyz
      hsSecond hxSecond hySecond hzSecond

  rcases hterm with hthree | hexact
  · exact Or.inl hthree
  · right
    obtain ⟨u₁,u₂,o₁,o₂,
      hu12,hu1o1,hu1o2,hu2o1,hu2o2,ho12,
      hu1Mem,hu2Mem,ho1Mem,ho2Mem,
      hu1Support,hu2Support,ho1Support,ho2Support,
      cert₁,cert₂,hqe1,hqe2,_hidden1,_hidden2⟩ := hexact

    have hwhole :=
      planar_exactTwo_QTTT_force_whole_cube_QT_pair
        hp hcap hn3 hdelta0 hdeltaHalf ht hlam C
        hsx hsy hsz hxy hxz hyz
        ho12
        hu1o1.symm hu2o1.symm
        hu1o2.symm hu2o2.symm
        hu12
        ho1Mem ho2Mem hu1Mem hu2Mem
        hsLoss hxLoss hyLoss hzLoss
        hsSecond hxSecond hySecond hzSecond
        ho1Support ho2Support hu1Support hu2Support
        cert₁ cert₂ hqe1 hqe2
        hcx hcy hcz hcxy hcxz hcyz
        hsActive hsQ hxT hyT hzT

    rcases hwhole with hxWhole | hyWhole | hzWhole
    · exact Or.inl ⟨hxWhole.1, hxWhole.2⟩
    · exact Or.inr (Or.inl ⟨hyWhole.1, hyWhole.2⟩)
    · exact Or.inr (Or.inr ⟨hzWhole.1, hzWhole.2⟩)

#print axioms planar_QTTT_threeSupport_or_wholeCube

end ProjectionOrdered
end JSP000404Research
