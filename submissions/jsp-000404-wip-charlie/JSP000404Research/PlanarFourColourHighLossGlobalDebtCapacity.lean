import JSP000404Research.PlanarFourColourHighLossReuseUniqueTop
import JSP000404Research.ActualOneHighLossCentreGlobalDebtCapacity
import Mathlib.Tactic

/-!
# Genuine n=4 planar AngleCap global original translated-loss debt capacity

For a real planar four-colour lower branch with >=3 actual original
centres, all exponents are <=3 and AngleCap excludes two distinct top
exponent 3 centres. Consequently the ACTUAL projected-loss high-centre
pool has size <=1, so original eighth-lane translated-loss debt is
bounded by the number of low (<=2) loss centres times the number of
distinct original opposite Boolean candidate words.

This is an actual planar consequence (no assumed "at most one high"
side condition), but it does NOT establish true exterior hole eligibility
or nonreusing dyadic payment of the other seven source classes.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_four_colour_original_duplicate_debt_le_low_loss_mul_opposites
    {V : Type*} [Fintype V] {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hcard : 3 ≤ Fintype.card V)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (4 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (cycles :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let htpos : 0 < t := by rw [ht]; linarith
    let hwidth : t < (4 : ℝ) + 1 := by rw [ht]; linarith
    let D := genericDirectionData_sendov hp hcap htpos hlam
    let B := standardResidualColoring D 4 (by exact_mod_cast hwidth)
    let k : ProjectionOrdered V → ℕ :=
      fun i => centreExponent (cycles i) t
    ∀ choice : ProjectionOrdered V → Fin 4,
      translatedLossDuplicateDebt B k choice ≤
        ((projectedLossVertices B k).filter
          (fun v => k v ≤ 2)).card *
        (actualLossEarliestOppositeCandidateWords B k choice).card := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have htpos : 0 < t := by rw [ht]; linarith
  have hwidth : t < (4 : ℝ) + 1 := by rw [ht]; linarith
  let D := genericDirectionData_sendov hp hcap htpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (4+1) :=
    standardResidualColoring D 4 (by exact_mod_cast hwidth)
  let k : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (cycles i) t
  change ∀ choice : ProjectionOrdered V → Fin 4,
    translatedLossDuplicateDebt B k choice ≤
      ((projectedLossVertices B k).filter
        (fun v => k v ≤ 2)).card *
      (actualLossEarliestOppositeCandidateWords B k choice).card
  have hdelta1 : delta < 1 := by linarith
  have hcardRe : 3 ≤ Fintype.card (ProjectionOrdered V) := by
    let e : ProjectionOrdered V ≃ V :=
      { toFun := ProjectionOrdered.toOriginal
        invFun := ProjectionOrdered.ofOriginal
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have heq : Fintype.card (ProjectionOrdered V) = Fintype.card V :=
      Fintype.card_congr e
    omega
  have hunique (v u : ProjectionOrdered V)
      (hv : k v = 3) (hu : k u = 3) : v = u := by
    by_contra hne
    have hvTop : centreExponent (cycles v) t = 4-1 := by
      simpa only [k,Nat.reduceSub] using hv
    have huTop : centreExponent (cycles u) t = 4-1 := by
      simpa only [k,Nat.reduceSub] using hu
    exact top_exponent_unique_of_card_ge_three
      (reindexedPoint_injective hp)
      (angleCap_reindexedPoint hp hcap)
      (by decide : 3 ≤ (4 : ℕ)) hcardRe
      hdelta0 hdeltaHalf ht hlam cycles v u hne hvTop huTop
  have hbound (v : ProjectionOrdered V) : k v ≤ 3 := by
    have hk := centreExponent_lt_n
      (cycles v) 4 delta t (by decide : 1 ≤ (4 : ℕ))
      hdelta0 hdelta1 ht
    dsimp only [k]
    omega
  have hhigh :
      ((projectedLossVertices B k).filter
        (fun v => 3 ≤ k v)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro v hv u hu
    have hv' : 3 ≤ k v := (Finset.mem_filter.mp hv).2
    have hu' : 3 ≤ k u := (Finset.mem_filter.mp hu).2
    have hvbound : k v ≤ 3 := hbound v
    have hubound : k u ≤ 3 := hbound u
    apply hunique v u <;> omega
  intro choice
  exact actual_one_high_loss_centre_global_duplicate_debt_le_low_mul_candidates
    B k choice hhigh

#print axioms planar_four_colour_original_duplicate_debt_le_low_loss_mul_opposites

end ProjectionOrdered
end JSP000404Research
