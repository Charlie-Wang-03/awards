import JSP000404Research.CompensatedDeletion
import Mathlib.Tactic

/-!
# Gain-closed cores for compensated deletion

A surprisingly weak structural condition is enough for the weighted induction.

Let `gain r i` mean that deleting centre `r` raises the exponent at surviving
centre `i` by at least one.  Suppose a nonempty finite set `S` is
gain-closed: every `r in S` has some distinct gain target `i in S`.

Choose a centre of minimum old exponent in `S`.  Its gain target has exponent
at least as large, so that single target's old dyadic weight already pays for
the deleted centre.  Thus no global extremizer classification is needed.
-/

namespace JSP000404Research

open scoped BigOperators

/-- A nonempty gain-closed finite core contains an edge from a minimum-exponent
centre to a centre of at least the same exponent. -/
theorem exists_payable_gain_edge
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (gain : V → V → Prop)
    (S : Finset V)
    (hS : S.Nonempty)
    (hclosed : ∀ r ∈ S, ∃ i ∈ S, i ≠ r ∧ gain r i) :
    ∃ r ∈ S, ∃ i ∈ S,
      i ≠ r ∧ gain r i ∧ exponent r ≤ exponent i := by
  classical
  let Core := {x : V // x ∈ S}
  let r0 : Core := ⟨hS.choose, hS.choose_spec⟩
  letI : Nonempty Core := ⟨r0⟩
  obtain ⟨r, hrmin⟩ :=
    Finite.exists_min (fun x : Core => exponent x.1)
  obtain ⟨i, hiS, hir, hgain⟩ :=
    hclosed r.1 r.2
  let ii : Core := ⟨i, hiS⟩
  have hweight : exponent r.1 ≤ exponent i := by
    simpa [ii] using hrmin ii
  exact ⟨r.1, r.2, i, hiS, hir, hgain, hweight⟩

/-- Abstract general induction from a gain-closed core.

For each possible deleted centre `r`, `after r i` is the exponent of
survivor `i` in the smaller configuration.  Exponents must never decrease;
every gain edge gives at least one unit of increase; and the smaller
configuration is assumed to satisfy the inductive weight bound.
-/
theorem compensated_induction_of_gain_closed_core
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (gain : V → V → Prop)
    (S : Finset V) (bound : ℕ)
    (hS : S.Nonempty)
    (hclosed : ∀ r ∈ S, ∃ i ∈ S, i ≠ r ∧ gain r i)
    (hmono : ∀ r ∈ S, ∀ j ∈ Finset.univ.erase r,
      exponent j ≤ after r j)
    (hgain : ∀ r i, gain r i →
      exponent i + 1 ≤ after r i)
    (hind : ∀ r ∈ S,
      ∑ j ∈ Finset.univ.erase r, 2 ^ after r j ≤ bound) :
    ∑ j : V, 2 ^ exponent j ≤ bound := by
  obtain ⟨r, hrS, i, hiS, hir, hgri, hweight⟩ :=
    exists_payable_gain_edge exponent gain S hS hclosed
  apply compensated_deletion_of_single_gain
    exponent (after r) bound
  · exact hir.symm
  · exact hmono r hrS
  · exact hgain r i hgri
  · exact hweight
  · exact hind r hrS

#print axioms exists_payable_gain_edge
#print axioms compensated_induction_of_gain_closed_core

end JSP000404Research
