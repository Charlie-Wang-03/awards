import JSP000404Research.RefinedHardWordHallOutlet
import Mathlib.Tactic

/-!
# Near-perfect refined matching in an exact-one overweight configuration

If

  hardCard = refinedTargetCard + 1,

then after removing any distinguished hard word x0, the remaining hard-word
type has exactly the same finite cardinality as

  Boolean holes ⊕ remaining strict-payment surplus tokens.

Hence there is a noncomputable equivalence, and in particular an injection,
between all hard demands except x0 and the complete refined credit space.

This packages the exact-one deficiency into the strongest possible finite
matching statement: every hard word except one can be paid perfectly.  The
remaining proof task is therefore to manufacture one additional credit for a
suitably chosen distinguished hard word.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

abbrev HardProjectionWordExcept
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (x0 : HardProjectionWord C exponent) :=
  {x : Fin n → Bool //
    x ∈ (hardProjectionWords C exponent).erase x0.1}

/-- Exact-one overweight gives a near-perfect equivalence after deleting any
one distinguished hard word. -/
noncomputable def hardExcept_equiv_refinedTarget_of_target_eq_bound_add_one
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (htarget :
      (∑ v, 2 ^ exponent v) = 2 ^ n + 1)
    (x0 : HardProjectionWord C exponent) :
    HardProjectionWordExcept C exponent x0 ≃
      ProjectionHoleOrRemainingSurplus C exponent := by
  classical
  apply Fintype.equivOfCardEq
  have hhard :=
    hardProjectionWords_card_eq_holes_add_remainingSurplus_add_one
      C exponent hexp honeLoss htarget
  have hx0 :
      x0.1 ∈ hardProjectionWords C exponent :=
    x0.2
  have hleft :
      Fintype.card (HardProjectionWordExcept C exponent x0) =
        (hardProjectionWords C exponent).card - 1 := by
    change
      ((hardProjectionWords C exponent).erase x0.1).card =
        (hardProjectionWords C exponent).card - 1
    rw [Finset.card_erase_of_mem hx0]
  have hright :
      Fintype.card
          (ProjectionHoleOrRemainingSurplus C exponent)
        =
      (projectionHoleWords C).card +
        remainingStrictPaymentSurplus C exponent := by
    simp [ProjectionHoleOrRemainingSurplus,
      ProjectionHoleWord,
      Fintype.card_sum,
      Fintype.card_coe,
      Fintype.card_fin]
  rw [hleft, hright]
  omega

/-- Injection form of the near-perfect matching. -/
theorem exists_hardExcept_injection_to_refinedTarget
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (htarget :
      (∑ v, 2 ^ exponent v) = 2 ^ n + 1)
    (x0 : HardProjectionWord C exponent) :
    ∃ f :
        HardProjectionWordExcept C exponent x0 →
          ProjectionHoleOrRemainingSurplus C exponent,
      Function.Injective f := by
  let e :=
    hardExcept_equiv_refinedTarget_of_target_eq_bound_add_one
      C exponent hexp honeLoss htarget x0
  exact ⟨e, e.injective⟩

/-- The near-perfect matching is actually onto the entire refined credit
space. -/
theorem hardExcept_equiv_refinedTarget_surjective
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (htarget :
      (∑ v, 2 ^ exponent v) = 2 ^ n + 1)
    (x0 : HardProjectionWord C exponent) :
    Function.Surjective
      (hardExcept_equiv_refinedTarget_of_target_eq_bound_add_one
        C exponent hexp honeLoss htarget x0) :=
  (hardExcept_equiv_refinedTarget_of_target_eq_bound_add_one
    C exponent hexp honeLoss htarget x0).surjective

#print axioms hardExcept_equiv_refinedTarget_of_target_eq_bound_add_one
#print axioms exists_hardExcept_injection_to_refinedTarget

end OrderedEdgeColoring
end JSP000404Research
