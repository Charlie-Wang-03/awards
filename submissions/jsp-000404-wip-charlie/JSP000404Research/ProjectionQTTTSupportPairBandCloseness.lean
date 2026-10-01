import JSP000404Research.ResidualSecondLayerTripleCanonical
import JSP000404Research.ProjectionUnitSupportTwoConsecutiveBands
import JSP000404Research.ResidualConsecutivePaletteCloseness
import Mathlib.Tactic

/-!
# Owner-coordinate closeness for a support-two translated pair in Q/T/T/T

For two translated projected-loss owners x,y, their connecting retained edge
has colour cx or cy.  Hence one endpoint sees both owner coordinates as
retained active colours.  If both endpoints are unit-transition support-two
centres, each has a consecutive three-colour retained palette, so cx and cy
differ by at most two band labels.
-/

namespace JSP000404Research
namespace ProjectionOrdered

theorem QTT_supportTwo_translated_pair_owner_labels_two_step_close
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
    (Cfam :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    {x y : ProjectionOrdered V}
    (hxy : x ≠ y)
    {word : Fin n → Bool}
    {cx cy : Fin n}
    (hxLoss :
      x ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (hyLoss :
      y ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (hxSecond : centreExponent (Cfam x) t = n - 2)
    (hySecond : centreExponent (Cfam y) t = n - 2)
    (hxSupport :
      positiveSupport (centreQuotient (Cfam x) t) = 2)
    (hySupport :
      positiveSupport (centreQuotient (Cfam y) t) = 2)
    (certX :
      HighExponentTransitionIntervalCertificate
        (reindexedPoint_injective hp) t x (Cfam x))
    (certY :
      HighExponentTransitionIntervalCertificate
        (reindexedPoint_injective hp) t y (Cfam y))
    (hqeX : certX.qe = 1)
    (hqeY : certY.qe = 1)
    (hcx :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      cx ∈ retainedActive R x)
    (hcy :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      cy ∈ retainedActive R y)
    (hxT :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      word ∈ translatedCompletionWords R x cx)
    (hyT :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      word ∈ translatedCompletionWords R y cy) :
    cx.val ≤ cy.val + 2 ∧
    cy.val ≤ cx.val + 2 := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let R :=
    planarStandardResidualColoring
      hp hcap (by omega : 1 ≤ n)
      hdelta0 (by linarith : delta < 1) ht hlam
  let exponent := planarCentreExponent hp Cfam

  have hxLoss' : x ∈ projectedLossVertices R exponent := by
    simpa [R,exponent] using hxLoss
  have hyLoss' : y ∈ projectedLossVertices R exponent := by
    simpa [R,exponent] using hyLoss
  have hcx' : cx ∈ retainedActive R x := by
    simpa [R] using hcx
  have hcy' : cy ∈ retainedActive R y := by
    simpa [R] using hcy
  have hxT' : word ∈ translatedCompletionWords R x cx := by
    simpa [R] using hxT
  have hyT' : word ∈ translatedCompletionWords R y cy := by
    simpa [R] using hyT

  obtain ⟨mx,hpalX⟩ :=
    planar_projectedLoss_unitSupportTwo_retainedPalette_consecutive
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      Cfam x hxLoss hxSecond hxSupport certX hqeX
  obtain ⟨my,hpalY⟩ :=
    planar_projectedLoss_unitSupportTwo_retainedPalette_consecutive
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      Cfam y hyLoss hySecond hySupport certY hqeY

  have hprofile :=
    genericProjection_lowerBranch_profile_hypotheses
      hp hcap (by omega : 1 ≤ n)
      hdelta0 (by linarith : delta < 1) ht hlam Cfam
  have hexp : ∀ q, exponent q ≤ n := by
    intro q
    exact Nat.le_of_lt
      (by simpa [exponent] using hprofile.1 q)
  have hone :
      ∀ q, (active R q).card ≤ n - exponent q + 1 := by
    intro q
    simpa [R,exponent] using hprofile.2 q

  have hedge :=
    OrderedEdgeColoring.QTT_translated_edge_colour_one_of_owners
      R exponent hexp hone
      hxy hxLoss' hyLoss'
      hcx' hcy' hxT' hyT'

  rcases hedge with hforward | hbackward
  · obtain ⟨hxylt,hret,hcol⟩ := hforward
    rcases hcol with hcolX | hcolY
    · have hcxAtY :
          cx ∈ retainedActive R y := by
        have hc :=
          OrderedEdgeColoring.retainedColor_mem_retainedActive_right
            R hxylt hret
        simpa [hcolX] using hc
      have hpalY' :
          (retainedActive R y).map Fin.valEmbedding =
            {my,my+1,my+2} := by
        simpa [R] using hpalY
      exact
        OrderedEdgeColoring.retained_labels_two_step_close_of_consecutive
          R hpalY' hcxAtY hcy'
    · have hcyAtX :
          cy ∈ retainedActive R x := by
        have hc :=
          OrderedEdgeColoring.retainedColor_mem_retainedActive_left
            R hxylt hret
        simpa [hcolY] using hc
      have hpalX' :
          (retainedActive R x).map Fin.valEmbedding =
            {mx,mx+1,mx+2} := by
        simpa [R] using hpalX
      exact
        OrderedEdgeColoring.retained_labels_two_step_close_of_consecutive
          R hpalX' hcx' hcyAtX
  · obtain ⟨hyxlt,hret,hcol⟩ := hbackward
    rcases hcol with hcolX | hcolY
    · have hcxAtY :
          cx ∈ retainedActive R y := by
        have hc :=
          OrderedEdgeColoring.retainedColor_mem_retainedActive_left
            R hyxlt hret
        simpa [hcolX] using hc
      have hpalY' :
          (retainedActive R y).map Fin.valEmbedding =
            {my,my+1,my+2} := by
        simpa [R] using hpalY
      exact
        OrderedEdgeColoring.retained_labels_two_step_close_of_consecutive
          R hpalY' hcxAtY hcy'
    · have hcyAtX :
          cy ∈ retainedActive R x := by
        have hc :=
          OrderedEdgeColoring.retainedColor_mem_retainedActive_right
            R hyxlt hret
        simpa [hcolY] using hc
      have hpalX' :
          (retainedActive R x).map Fin.valEmbedding =
            {mx,mx+1,mx+2} := by
        simpa [R] using hpalX
      exact
        OrderedEdgeColoring.retained_labels_two_step_close_of_consecutive
          R hpalX' hcx' hcyAtX

#print axioms QTT_supportTwo_translated_pair_owner_labels_two_step_close

end ProjectionOrdered
end JSP000404Research
