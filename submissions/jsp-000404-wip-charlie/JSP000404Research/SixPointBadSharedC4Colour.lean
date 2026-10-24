import JSP000404Research.SixPointBadActiveC4
import JSP000404Research.FiveMinimaC4UniqueCanary
import Mathlib.Tactic

/-!
# A single shared C4 colour for two genuine bad minima

The exact 3,3,2,2,2 profile forces each bad minimum to be active in a
colour class containing a four-cycle.  The five-minimum uniqueness lemma
then forces both certificates to use the *same* colour.

This is a strengthening of the conditional six-point branch, not an
unconditional original-plane dyadic-capacity theorem.  In particular,
active in a C4 colour does not imply lying on its four-cycle.
-/

namespace JSP000404Research

open BinaryEdgePartition

/-- Both exceptional minima must use the *same* C4-bearing colour. -/
theorem two_bad_minima_share_monochromatic_fourCycle_colour
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top bad₁ bad₂ : V) (root : Fin k)
    (htb₁ : top ≠ bad₁) (htb₂ : top ≠ bad₂)
    (hb₁₂ : bad₁ ≠ bad₂)
    (hcard : Fintype.card V = 6)
    (hrootTop : active P top = {root})
    (hrootEdges :
      ∀ {u v : V}, u < v →
        u ≠ top → v ≠ top →
        P.edgeColor u v ≠ root)
    (hBad₁ : ((active P bad₁).erase root).card = 3)
    (hBad₂ : ((active P bad₂).erase root).card = 3)
    (hOther :
      ∀ v : V,
        v ≠ top → v ≠ bad₁ → v ≠ bad₂ →
        ((active P v).erase root).card = 2) :
    ∃ c : Fin k,
      c ≠ root ∧ c ∈ active P bad₁ ∧
      c ∈ active P bad₂ ∧
      HasFourCycle (localColourGraph P top c) := by
  classical
  obtain ⟨c, hcRoot, hcBad₁, hcC4⟩ :=
    bad_minimum_active_in_some_monochromatic_fourCycle
      P top bad₁ bad₂ root htb₁ htb₂ hb₁₂ hcard
      hrootTop hrootEdges hBad₁ hBad₂ hOther
      bad₁ (Or.inl rfl)
  obtain ⟨d, hdRoot, hdBad₂, hdC4⟩ :=
    bad_minimum_active_in_some_monochromatic_fourCycle
      P top bad₁ bad₂ root htb₁ htb₂ hb₁₂ hcard
      hrootTop hrootEdges hBad₁ hBad₂ hOther
      bad₂ (Or.inr rfl)
  have hcd : c = d := by
    by_contra hne
    exact disjoint_graphs_on_five_not_both_C4
      (card_otherVertex_eq_five_of_card_six hcard top)
      (localColourGraph P top c)
      (localColourGraph P top d)
      (localColourGraph_edgeFinset_disjoint_of_ne P top hne)
      hcC4 hdC4
  refine ⟨c, hcRoot, hcBad₁, ?_, hcC4⟩
  simpa [hcd] using hdBad₂

#print axioms two_bad_minima_share_monochromatic_fourCycle_colour

end JSP000404Research
