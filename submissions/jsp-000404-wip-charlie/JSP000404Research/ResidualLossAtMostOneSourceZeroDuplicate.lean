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

/-- STRONGER: with at most one projected-loss source, the EXACT
cross-coordinate duplicate debt is zero for EVERY flip choice, active or
otherwise. This uses NO exponent bound, no n≥1, no original geometry
and no choice construction: a cross-slice collision itself demands
TWO different projected-loss owners with different chosen colours. -/
theorem any_choice_duplicate_zero_of_at_most_one_projected_loss_source
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n)
    (hone : (projectedLossVertices C exponent).card ≤ 1) :
    translatedLossDuplicateDebt C exponent choice = 0 := by
  classical
  by_contra hneZero
  have hpositive :
      0 < translatedLossDuplicateDebt C exponent choice :=
    Nat.pos_of_ne_zero hneZero
  obtain ⟨c,d,hcd,word,hwordC,hwordD⟩ :=
    positive_loss_duplicateDebt_has_slice_collision
      C exponent choice hpositive
  obtain ⟨v,hvSlice,_⟩ := Finset.mem_biUnion.mp hwordC
  obtain ⟨u,huSlice,_⟩ := Finset.mem_biUnion.mp hwordD
  have hvData :=
    (mem_lossCoordinateSlice C exponent choice c v).1 hvSlice
  have huData :=
    (mem_lossCoordinateSlice C exponent choice d u).1 huSlice
  have hvu : v = u := by
    by_contra hvune
    have htwo : 1 < (projectedLossVertices C exponent).card :=
      Finset.one_lt_card.mpr ⟨v,hvData.1,u,huData.1,hvune⟩
    omega
  have hcd' : c = d := by
    calc
      c = choice v := hvData.2.symm
      _ = choice u := congrArg choice hvu
      _ = d := huData.2
  exact hcd hcd'

#print axioms any_choice_duplicate_zero_of_at_most_one_projected_loss_source

#print axioms at_most_one_projected_loss_vertex_has_active_zero_duplicate_choice
end OrderedEdgeColoring
end JSP000404Research
