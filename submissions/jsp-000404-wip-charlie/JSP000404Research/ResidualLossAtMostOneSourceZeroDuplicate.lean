import JSP000404Research.ResidualLossCommonActiveColourNoDuplicate
import JSP000404Research.ResidualLossActiveFlipBlocker
import Mathlib.Tactic

/-!
# NO EXTRA HYPOTHESIS on flip choice: at most one actual loss source
  means the entire projected-loss duplicate debt CAN BE ELIMINATED

Assume the verified ordinary exponent bound k(v) ≤ n, with n≥1.
Every genuinely projected-loss vertex has a nonempty retained-active
palette. If there is at most ONE such source, select one active colour
at that source and the same colour elsewhere. This is a globally
defined active flip choice whose translated-loss slices are pairwise
disjoint. It pays ZERO cross-coordinate duplicate debt, without any
unproved true hole or surplus credit and without requiring AngleCap.

This is a genuine no-collision source-class elimination for the
one-source branch of the original six-source ledger; it does not
eliminate the remaining terminal debt or covered blockers.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem at_most_one_projected_loss_vertex_has_active_zero_duplicate_choice
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (hn : 1 ≤ n)
    (hone :
      (projectedLossVertices C exponent).card ≤ 1) :
    ∃ choice : V → Fin n,
      (∀ v ∈ projectedLossVertices C exponent,
        choice v ∈ retainedActive C v) ∧
      translatedLossDuplicateDebt C exponent choice = 0 := by
  classical
  by_cases hSome : (projectedLossVertices C exponent).Nonempty
  · obtain ⟨v,hv⟩ := hSome
    obtain ⟨c0,hc0⟩ :=
      projectedLoss_retainedActive_nonempty C exponent hexp hv
    apply common_retained_active_colour_gives_zero_loss_duplicate_choice
      C exponent c0
    intro w hw
    have hwv : w = v := by
      by_contra hne
      have htwo : 1 < (projectedLossVertices C exponent).card :=
        Finset.one_lt_card.mpr ⟨w,hw,v,hv,hne⟩
      omega
    simpa only [hwv] using hc0
  · apply common_retained_active_colour_gives_zero_loss_duplicate_choice
      C exponent ⟨0, by omega⟩
    intro v hv
    exact False.elim (hSome ⟨v,hv⟩)

#print axioms at_most_one_projected_loss_vertex_has_active_zero_duplicate_choice
end OrderedEdgeColoring
end JSP000404Research
