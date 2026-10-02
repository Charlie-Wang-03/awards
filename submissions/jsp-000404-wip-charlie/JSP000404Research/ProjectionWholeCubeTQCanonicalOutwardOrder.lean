import JSP000404Research.ProjectionOrderCanonicalOrder
import JSP000404Research.ResidualWholeCubeTQOutwardOrder
import JSP000404Research.ProjectionStandardBandBudget
import Mathlib.Tactic

/-!
# Canonical-order form of whole-cube T/Q outward rigidity

The residual whole-cube T/Q augmentation theorem says that, whenever the
augmenting source x and its partner y lie on the same side of the completion
owner s, x cannot be farther from s than y.

Because the generic projection order agrees with CanonicalPointLt, this file
restates that conclusion directly in canonical planar order.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_wholeCube_TQ_partner_closer_in_canonical_order
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (Cfam :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    {s x y : ProjectionOrdered V}
    (hsx : s ≠ x)
    (hsy : s ≠ y)
    (hxy : x ≠ y)
    {common extra : Fin n → Bool}
    {cx cy d : Fin n}
    (hxLoss :
      x ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam)
        (planarCentreExponent hp Cfam))
    (hyLoss :
      y ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam)
        (planarCentreExponent hp Cfam))
    (hcx :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam
      cx ∈ retainedActive R x)
    (hcy :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam
      cy ∈ retainedActive R y)
    (hcxy : cx ≠ cy)
    (hdx :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam
      d ∈ retainedActive R x)
    (hdcx : d ≠ cx)
    (hsQ :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam
      common ∈ retainedCompletionWords R s)
    (hxT :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam
      common ∈ translatedCompletionWords R x cx)
    (hyT :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam
      common ∈ translatedCompletionWords R y cy)
    (hxExtra :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam
      extra ∈ translatedCompletionWords R x d)
    (hyExtra :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam
      extra ∈ retainedCompletionWords R y) :
    ¬ (
      (CanonicalPointLt p x.toOriginal y.toOriginal ∧
       CanonicalPointLt p y.toOriginal s.toOriginal)
      ∨
      (CanonicalPointLt p s.toOriginal y.toOriginal ∧
       CanonicalPointLt p y.toOriginal x.toOriginal)
    ) := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let R :=
    planarStandardResidualColoring
      hp hcap hn hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp Cfam

  have hprofile :=
    genericProjection_lowerBranch_profile_hypotheses
      hp hcap hn hdelta0 hdelta1 ht hlam Cfam
  have hexp : ∀ q, exponent q ≤ n := by
    intro q
    exact Nat.le_of_lt
      (by simpa [exponent] using hprofile.1 q)
  have hone :
      ∀ q, (active R q).card ≤ n - exponent q + 1 := by
    intro q
    simpa [R,exponent] using hprofile.2 q

  have hraw :=
    QTT_second_TQ_forces_partner_closer_on_same_side
      R exponent hexp hone
      hsx hsy hxy
      (by simpa [R,exponent] using hxLoss)
      (by simpa [R,exponent] using hyLoss)
      (by simpa [R] using hcx)
      (by simpa [R] using hcy)
      hcxy
      (by simpa [R] using hdx)
      hdcx
      (by simpa [R] using hsQ)
      (by simpa [R] using hxT)
      (by simpa [R] using hyT)
      (by simpa [R] using hxExtra)
      (by simpa [R] using hyExtra)

  intro hbad
  apply hraw
  rcases hbad with hleft | hright
  · exact Or.inl
      ⟨(canonicalPointLt_iff_projection_lt hp x y).1 hleft.1,
       (canonicalPointLt_iff_projection_lt hp y s).1 hleft.2⟩
  · exact Or.inr
      ⟨(canonicalPointLt_iff_projection_lt hp s y).1 hright.1,
       (canonicalPointLt_iff_projection_lt hp y x).1 hright.2⟩

#print axioms planar_wholeCube_TQ_partner_closer_in_canonical_order

end ProjectionOrdered
end JSP000404Research
