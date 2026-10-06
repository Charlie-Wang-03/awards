import JSP000404Research.ResidualWholeCubeSecondCoordinateCore
import JSP000404Research.ResidualWholeCubeSecondCoordinateProfile
import JSP000404Research.ResidualEnlargedLossCollisionSemantics
import Mathlib.Tactic

/-!
# T/Q versus T/T semantics of the whole-cube second-coordinate terminal

In the residual second-coordinate terminal both v and the third core source w
are projected-loss vertices.

The augmenting word lies in T_d(v) and in the enlarged loss block B_w.
Therefore exactly two structural possibilities remain:

* T/Q: the word lies in Q_w; then the retained edge vw has colour d.
* T/T: the word lies in a translated slice T_e(w); then e != d and the
  retained edge vw has colour d or e.

The distinctness e != d follows from disjointness of equal-coordinate
translated cubes at distinct loss vertices.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem wholeCubeSecondCoordinate_secondLayer_TQ_or_TT
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {T : Finset V}
    {s v : V} {c : Fin n}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwit :
      WholeCubeSecondCoordinateSecondLayerWitness
        C exponent T s v c) :
    WholeCubeSecondCoordinateTQ C exponent T s v c
    ∨
    WholeCubeSecondCoordinateTT C exponent T s v c := by
  obtain ⟨word,w,d,hdActive,hdc,hdWord,
      hwBlock,hwT,hwNeV,hwNeS,hwLoss,hwSecond⟩ := hwit

  have hsem :=
    loss_translated_collision_with_enlarged_block_edge_semantics
      C exponent hexp honeLoss
      hvLoss hwNeV hdActive hdWord hwBlock

  rcases hsem with hnon | hloss
  · exact False.elim (hnon.1 hwLoss)
  · rcases hloss.2 with hQ | hT
    · left
      exact ⟨word,w,d,
        hdActive,hdc,hdWord,hQ.1,
        hwT,hwNeV,hwNeS,hwLoss,hwSecond,hQ.2⟩
    · right
      obtain ⟨e,heActive,heWord,hedge⟩ := hT
      have hde : e ≠ d := by
        intro hed
        subst e
        have hinter :
            (translatedCompletionWords C v d ∩
              translatedCompletionWords C w d).Nonempty :=
          ⟨word,Finset.mem_inter.mpr ⟨hdWord,heWord⟩⟩
        have hdistinct :=
          translated_loss_conflict_distinct_coordinates
            C exponent hexp honeLoss
            hvLoss hwLoss hwNeV hinter
        exact hdistinct rfl
      exact Or.inr
        ⟨word,w,d,e,
          hdActive,hdc,heActive,hde,
          hdWord,heWord,
          hwT,hwNeV,hwNeS,hwLoss,hwSecond,hedge⟩

#print axioms wholeCubeSecondCoordinate_secondLayer_TQ_or_TT

end OrderedEdgeColoring
end JSP000404Research
