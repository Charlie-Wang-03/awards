import JSP000404Research.ResidualWholeCubeSecondCoordinateCore
import JSP000404Research.ResidualLossCollisionCore
import Mathlib.Tactic

/-!
# Lightweight T/Q versus T/T split for the second-coordinate witness

This is the local semantic split used by profiled whole-cube recursion.
It deliberately avoids minimal-Hall and global capacity machinery.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem wholeCubeSecondCoordinate_secondLayer_TQ_or_TT_core
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
    loss_translated_collision_with_enlarged_block_edge_semantics_core
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
        exact
          (translated_loss_conflict_distinct_coordinates_core
            C exponent hexp honeLoss
            hvLoss hwLoss hwNeV hinter) rfl
      exact Or.inr
        ⟨word,w,d,e,
          hdActive,hdc,heActive,hde,
          hdWord,heWord,
          hwT,hwNeV,hwNeS,hwLoss,hwSecond,hedge⟩

#print axioms wholeCubeSecondCoordinate_secondLayer_TQ_or_TT_core

end OrderedEdgeColoring
end JSP000404Research
