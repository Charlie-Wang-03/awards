import JSP000404Research.TurnUnitSlots
import JSP000404Research.SharpDeficit
import Mathlib.Tactic

/-!
# Exact turn-unit slot count at the six-point top centre

A top centre has exponent n-1.  In the lower Sendov branch its quotient vector
has unit deficit, so SharpDeficit gives exact quotient mass n.  Since the
turn-unit slot type has one element for each whole quotient unit, its
cardinality is exactly n.

This is the sharp counting input for simultaneously avoiding q=1 critical
obstructions and top saturation obstructions.
-/

namespace JSP000404Research

theorem centreTurnUnitSlot_card_eq_n_of_exponent_n_sub_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hexp : centreExponent C t = n - 1) :
    Fintype.card (CentreTurnUnitSlot C t) = n := by
  have hdelta1 : delta < 1 := by linarith
  have hQ :
      (∑ r, centreQuotient C t r) ≤ n :=
    centreQuotient_function_sum_le_n
      C n delta t (by omega : 1 ≤ n)
      hdelta0 hdelta1 ht
  have hdef :
      n - floorExcess (centreQuotient C t) = 1 := by
    rw [← show centreExponent C t =
      floorExcess (centreQuotient C t) by rfl, hexp]
    omega
  have hsum :
      (∑ r, centreQuotient C t r) = n :=
    (unit_deficit_structure
      (centreQuotient C t) n
      (by omega : 2 ≤ n) hQ hdef).2
  rw [centreTurnUnitSlot_card_eq_quotient_sum C t]
  exact hsum

#print axioms centreTurnUnitSlot_card_eq_n_of_exponent_n_sub_one

end JSP000404Research
