import JSP000404Research.SixPointBadSharedC4Colour
import Mathlib.Tactic

/-!
# Exact six-point equality forces ONE C4 colour active at BOTH exceptions

The exact six-point equality profile produces a root colour, with
reduced active counts 3,3,2,2,2 and all minimum-minimum edges non-root.
The active-in-a-C4 incidence lemma, combined with the five-minimum
C4 uniqueness theorem, then produces a SINGLE C4-bearing colour
active at both exceptional minima.

This upgrades the profile-conditional shared-C4 result to the actual
six-point equality hypothesis. It is a local graph-theoretic reduction,
not the original AngleCap true-hole payment.
-/

namespace JSP000404Research

open BinaryEdgePartition

theorem six_point_two_exception_shared_C4_active_at_both
    {V : Type*} [LinearOrder V] [Fintype V]
    {n : ℕ}
    (hn : 4 ≤ n)
    (P : BinaryEdgePartition V n)
    (top bad₁ bad₂ : V)
    (htb₁ : top ≠ bad₁)
    (htb₂ : top ≠ bad₂)
    (hb₁₂ : bad₁ ≠ bad₂)
    (hcard : Fintype.card V = 6)
    (hTop : (active P top).card ≤ 1)
    (hBad₁ : (active P bad₁).card ≤ 4)
    (hBad₂ : (active P bad₂).card ≤ 4)
    (hOther :
      ∀ v : V,
        v ≠ top → v ≠ bad₁ → v ≠ bad₂ →
        (active P v).card ≤ 3) :
    ∃ c : Fin n,
      c ∈ active P bad₁ ∧ c ∈ active P bad₂ ∧
      HasFourCycle (localColourGraph P top c) := by
  obtain ⟨root, hrootTop, _hrootBits, hrootEdges,
    hredBad₁, hredBad₂, hredOther⟩ :=
    six_point_two_exception_root_factorization
      hn P top bad₁ bad₂ htb₁ htb₂ hb₁₂ hcard
      hTop hBad₁ hBad₂ hOther
  obtain ⟨c, _hcRoot, hcBad₁, hcBad₂, hcC4⟩ :=
    two_bad_minima_share_monochromatic_fourCycle_colour
      P top bad₁ bad₂ root htb₁ htb₂ hb₁₂ hcard
      hrootTop hrootEdges hredBad₁ hredBad₂ hredOther
  exact ⟨c, hcBad₁, hcBad₂, hcC4⟩

#print axioms six_point_two_exception_shared_C4_active_at_both

end JSP000404Research
