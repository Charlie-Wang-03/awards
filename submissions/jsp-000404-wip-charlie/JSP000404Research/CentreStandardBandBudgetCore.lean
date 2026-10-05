import JSP000404Research.LocalDirectionCycle
import JSP000404Research.CentreExponent
import JSP000404Research.StandardBandColor
import Mathlib.Tactic

/-!
# Lightweight centre/local-cycle standard-band budget

This module contains only the arithmetic bridge from a concrete local direction
cycle to the standard-band active-card bound.  It is intentionally separated
from higher support / palette geometry so projection-residual arguments do not
inherit unrelated proof dependencies.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

theorem centreExponent_add_incidentBands_card_le_of_local_agreement
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {hp : Function.Injective p}
    {t : ℝ} {n : ℕ} {i : V}
    (D : DirectionData V t)
    (L : LocalDirectionCycle D i)
    (C : CentreProjectiveCycle hp i)
    (ht : t < (n : ℝ) + 1)
    (hagree : L.exponent = centreExponent C t) :
    centreExponent C t + (D.incidentBands (n + 1) i).card ≤ n + 1 := by
  have h := L.exponent_add_incidentBands_card_le ht
  rw [hagree] at h
  exact h

theorem centreExponent_add_standardActive_card_le_of_local_agreement
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {hp : Function.Injective p}
    {t : ℝ} {n : ℕ} {i : V}
    (D : DirectionData V t)
    (L : LocalDirectionCycle D i)
    (C : CentreProjectiveCycle hp i)
    (hn : 0 < n + 1)
    (ht : t < (n : ℝ) + 1)
    (hagree : L.exponent = centreExponent C t) :
    centreExponent C t +
        (active
          (standardBandColoring D (n + 1) hn
            (by exact_mod_cast ht))
          i).card
      ≤ n + 1 := by
  rw [standardBand_active_eq_incidentBands]
  exact centreExponent_add_incidentBands_card_le_of_local_agreement
    D L C ht hagree

theorem standardActive_card_le_centreDeficit_add_one_of_local_agreement
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {hp : Function.Injective p}
    {t : ℝ} {n : ℕ} {i : V}
    (D : DirectionData V t)
    (L : LocalDirectionCycle D i)
    (C : CentreProjectiveCycle hp i)
    (ht : t < (n : ℝ) + 1)
    (hexp : centreExponent C t ≤ n)
    (hagree : L.exponent = centreExponent C t) :
    (active
      (standardBandColoring D (n + 1)
        (Nat.succ_pos n)
        (by exact_mod_cast ht))
      i).card
      ≤ n - centreExponent C t + 1 := by
  have h :=
    centreExponent_add_standardActive_card_le_of_local_agreement
      D L C (Nat.succ_pos n) ht hagree
  omega

#print axioms centreExponent_add_incidentBands_card_le_of_local_agreement
#print axioms centreExponent_add_standardActive_card_le_of_local_agreement
#print axioms standardActive_card_le_centreDeficit_add_one_of_local_agreement

end DirectionData
end JSP000404Research
