import JSP000404Research.NearPerfectRefinedHardMatching
import Mathlib.Tactic

/-!
# Rank-descent obstruction to an exact-one near-perfect matching

In an exact-one overweight configuration, deleting one distinguished hard word
gives a bijection from every other hard word to the complete refined credit
space (Boolean holes plus remaining strict-payment surplus tokens).

To contradict exact-one overweight it is therefore enough to give every hard
word a candidate refined credit with the following property:

* look at the hard word currently occupying that credit under the near-perfect
  bijection;
* its rank is strictly smaller than the rank of the requesting hard word.

Starting from the distinguished hard word would then produce an infinite
strictly descending sequence in Nat, which is impossible.

This module isolates that purely well-founded matching argument.  Geometry and
residual combinatorics only need to construct the candidate credit and prove
the rank decrease.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- The raw hard word occupying a refined credit under the near-perfect
matching obtained after erasing x0. -/
noncomputable def nearPerfectOccupant
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (htarget :
      (∑ v, 2 ^ exponent v) = 2 ^ n + 1)
    (x0 : HardProjectionWord C exponent)
    (credit : ProjectionHoleOrRemainingSurplus C exponent) :
    Fin n → Bool :=
  (hardExcept_equiv_refinedTarget_of_target_eq_bound_add_one
    C exponent hexp honeLoss htarget x0).symm credit

theorem nearPerfectOccupant_mem_hard
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (htarget :
      (∑ v, 2 ^ exponent v) = 2 ^ n + 1)
    (x0 : HardProjectionWord C exponent)
    (credit : ProjectionHoleOrRemainingSurplus C exponent) :
    nearPerfectOccupant C exponent hexp honeLoss htarget x0 credit
      ∈ hardProjectionWords C exponent := by
  let e :=
    hardExcept_equiv_refinedTarget_of_target_eq_bound_add_one
      C exponent hexp honeLoss htarget x0
  have hmem :
      (e.symm credit).1 ∈
        (hardProjectionWords C exponent).erase x0.1 :=
    (e.symm credit).2
  exact (Finset.mem_erase.mp hmem).2

theorem nearPerfectOccupant_ne_distinguished
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (htarget :
      (∑ v, 2 ^ exponent v) = 2 ^ n + 1)
    (x0 : HardProjectionWord C exponent)
    (credit : ProjectionHoleOrRemainingSurplus C exponent) :
    nearPerfectOccupant C exponent hexp honeLoss htarget x0 credit ≠ x0.1 := by
  let e :=
    hardExcept_equiv_refinedTarget_of_target_eq_bound_add_one
      C exponent hexp honeLoss htarget x0
  have hmem :
      (e.symm credit).1 ∈
        (hardProjectionWords C exponent).erase x0.1 :=
    (e.symm credit).2
  exact (Finset.mem_erase.mp hmem).1

/-- Pure well-founded core.

If every hard word can request one refined credit whose current near-perfect
occupant has strictly smaller natural-number rank, exact-one overweight is
impossible. -/
theorem false_of_nearPerfect_refinedTarget_rank_descent
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (htarget :
      (∑ v, 2 ^ exponent v) = 2 ^ n + 1)
    (x0 : HardProjectionWord C exponent)
    (rank : (Fin n → Bool) → ℕ)
    (target :
      HardProjectionWord C exponent →
        ProjectionHoleOrRemainingSurplus C exponent)
    (hdesc :
      ∀ x : HardProjectionWord C exponent,
        rank
          (nearPerfectOccupant
            C exponent hexp honeLoss htarget x0 (target x))
          < rank x.1) :
    False := by
  let occupant :
      HardProjectionWord C exponent →
        HardProjectionWord C exponent :=
    fun x =>
      ⟨nearPerfectOccupant
          C exponent hexp honeLoss htarget x0 (target x),
        nearPerfectOccupant_mem_hard
          C exponent hexp honeLoss htarget x0 (target x)⟩
  have hstep :
      ∀ x : HardProjectionWord C exponent,
        rank (occupant x).1 < rank x.1 := by
    intro x
    exact hdesc x
  have hno :
      ∀ k : ℕ,
        ∀ x : HardProjectionWord C exponent,
          rank x.1 = k → False := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro x hx
        have hlt : rank (occupant x).1 < k := by
          simpa [hx] using hstep x
        exact ih (rank (occupant x).1) hlt (occupant x) rfl
  exact hno (rank x0.1) x0 rfl

#print axioms nearPerfectOccupant_mem_hard
#print axioms nearPerfectOccupant_ne_distinguished
#print axioms false_of_nearPerfect_refinedTarget_rank_descent

end OrderedEdgeColoring
end JSP000404Research
