import JSP000404Research.ResidualLossCrossSliceCarrier
import Mathlib.Tactic

/-!
# Globally unique coordinate labels of actual cross-loss source pairs

Every genuine cross-coordinate collision source/blocker vertex pair
p=(v,w) has coordinate labels (choice v, choice w) determined
uniquely by its endpoints. A fixed oriented pair therefore cannot
be reused in *different* coordinate slices. Moreover, the global
later>earlier orientation makes double charging the REVERSED
oriented pair impossible.

This proves NONREUSE OF THE EDGE-PAIR INDEX in the first-hit
duplicate-debt ledger. It is not nonreuse of genuine Boolean holes,
nor of the Boolean words themselves.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- The chosen coordinate labels of a REAL cross-loss collision
pair are forced to equal the choices at its two endpoints. -/
theorem crossLossConflictPair_chosen_labels
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    {c d : Fin n} {p : V × V}
    (hp : p ∈ crossLossConflictPairs C exponent choice c d) :
    choice p.1 = c ∧ choice p.2 = d := by
  have hdata :=
    (mem_crossLossConflictPairs C exponent choice c d p.1 p.2).1 hp
  exact ⟨
    ((mem_lossCoordinateSlice C exponent choice c p.1).1 hdata.1).2,
    ((mem_lossCoordinateSlice C exponent choice d p.2).1 hdata.2.1).2⟩

/-- A fixed ordered pair of actual loss vertices cannot receive
two different selected flip-coordinate labels. -/
theorem crossLossConflictPair_unique_coordinate_pair
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    {c d e f : Fin n} {p : V × V}
    (hp : p ∈ crossLossConflictPairs C exponent choice c d)
    (hq : p ∈ crossLossConflictPairs C exponent choice e f) :
    c = e ∧ d = f := by
  have h1 := crossLossConflictPair_chosen_labels C exponent choice hp
  have h2 := crossLossConflictPair_chosen_labels C exponent choice hq
  exact ⟨h1.1.symm.trans h2.1, h1.2.symm.trans h2.2⟩

/-- Different ordered coordinate pairs have disjoint sets of
actual source/blocker loss-conflict vertex pairs. -/
theorem crossLossConflictPairs_disjoint_of_distinct_labels
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    {c d e f : Fin n}
    (hne : (c, d) ≠ (e, f)) :
    Disjoint (crossLossConflictPairs C exponent choice c d)
      (crossLossConflictPairs C exponent choice e f) := by
  classical
  rw [Finset.disjoint_left]
  intro p hp hq
  have hh :=
    crossLossConflictPair_unique_coordinate_pair
      C exponent choice hp hq
  exact hne (Prod.ext hh.1 hh.2)

/-- The same UNORDERED actual edge cannot be charged once with its
high chosen coordinate as the source and again in the reverse
orientation: the reversed high-coordinate relation would contradict
the first orientation. -/
theorem crossLossConflictPairs_no_reverse_high_coordinate
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    {v w : V} {c d e f : Fin n}
    (hdc : d < c) (hfe : f < e)
    (hp : (v, w) ∈ crossLossConflictPairs C exponent choice c d)
    (hq : (w, v) ∈ crossLossConflictPairs C exponent choice e f) :
    False := by
  have h1 := crossLossConflictPair_chosen_labels C exponent choice hp
  have h2 := crossLossConflictPair_chosen_labels C exponent choice hq
  have hfv : f = c := h2.2.symm.trans h1.1
  have hed : e = d := h2.1.symm.trans h1.2
  have hcontr : c < d := by
    simpa [hfv, hed] using hfe
  exact (lt_asymm hdc hcontr)

#print axioms crossLossConflictPair_chosen_labels
#print axioms crossLossConflictPair_unique_coordinate_pair
#print axioms crossLossConflictPairs_disjoint_of_distinct_labels
#print axioms crossLossConflictPairs_no_reverse_high_coordinate

end OrderedEdgeColoring
end JSP000404Research
