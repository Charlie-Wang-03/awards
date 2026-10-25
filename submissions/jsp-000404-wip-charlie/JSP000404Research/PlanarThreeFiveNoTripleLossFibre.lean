import JSP000404Research.ResidualLossTripleFibreSixCentreBarrier
import JSP000404Research.PlanarStandardResidualBudget
import JSP000404Research.CentreExponentBounds
import Mathlib.Tactic

/-!
# Actual planar five-centre exclusion of triple projected-loss collision fibres

First derive a universal original-source n=3 exclusion for <=5 centres and
exponent<=2. Then instantiate it with the GENUINE standard residual colouring
of any five-centre planar AngleCap configuration at t=3+delta,
0<=delta<1/2, and actual centre-projective exponents.

No invented holes, credits, injective payment, extra AngleCap hypotheses,
or replacement of the one genuine root sorry appear in this module.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A direct, unconditional no-triple-collision theorem for all
ACTUAL n=3 loss-slice systems on <=5 original vertices under the
genuine exponent<=2 bound. -/
theorem actual_three_colour_five_centre_no_triple_loss_fibre
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ)
    (choice : V → Fin 3)
    (hexp : ∀ v, exponent v ≤ 2)
    (hfive : Fintype.card V ≤ 5)
    (q : Fin 3 → Bool) :
    (actualLossOppositeCandidateFibre C exponent choice q).card ≤ 2 := by
  by_contra hnot
  have hthree : 3 ≤
      (actualLossOppositeCandidateFibre C exponent choice q).card := by
    omega
  have hsix :=
    actual_three_colour_triple_fibre_forces_six_centres
      C exponent choice hexp q hthree
  omega

#print axioms actual_three_colour_five_centre_no_triple_loss_fibre

end OrderedEdgeColoring

namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- TRUE planar AngleCap / standard residual colour n=3, up to FIVE
original centres, excludes all three-record genuine canonical
earliest-prior projected-loss collision fibres, for EVERY source
coordinate choice and target Boolean word. The exponent bound is
obtained from the true centre projective cycles, not assumed. -/
theorem planar_three_five_standard_no_triple_loss_fibre
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hfive : Fintype.card V ≤ 5)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (cycles :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let htpos : 0 < t := by
      rw [ht]
      linarith
    let hwidth : t < (3 : ℝ) + 1 := by
      rw [ht]
      linarith
    let D := genericDirectionData_sendov hp hcap htpos hlam
    let B := standardResidualColoring D 3 (by exact_mod_cast hwidth)
    let k : ProjectionOrdered V → ℕ :=
      fun i => centreExponent (cycles i) t
    ∀ (choice : ProjectionOrdered V → Fin 3) (q : Fin 3 → Bool),
      (actualLossOppositeCandidateFibre B k choice q).card ≤ 2 := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have htpos : 0 < t := by
    rw [ht]
    linarith
  have hwidth : t < (3 : ℝ) + 1 := by
    rw [ht]
    linarith
  let D := genericDirectionData_sendov hp hcap htpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (3 + 1) :=
    standardResidualColoring D 3 (by exact_mod_cast hwidth)
  let k : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (cycles i) t
  change ∀ (choice : ProjectionOrdered V → Fin 3) (q : Fin 3 → Bool),
      (actualLossOppositeCandidateFibre B k choice q).card ≤ 2
  have hdelta1 : delta < 1 := by linarith
  have hk : ∀ i : ProjectionOrdered V, k i ≤ 2 := by
    intro i
    have hi := centreExponent_lt_n
      (cycles i) 3 delta t (by decide : 1 ≤ (3 : ℕ))
      hdelta0 hdelta1 ht
    dsimp [k]
    omega
  have hsize : Fintype.card (ProjectionOrdered V) ≤ 5 := by
    have heq : Fintype.card (ProjectionOrdered V) = Fintype.card V := by
      let e : ProjectionOrdered V ≃ V :=
        { toFun := ProjectionOrdered.toOriginal
          invFun := ProjectionOrdered.ofOriginal
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact Fintype.card_congr e
    omega
  intro choice q
  exact actual_three_colour_five_centre_no_triple_loss_fibre
    B k choice hk hsize q

#print axioms planar_three_five_standard_no_triple_loss_fibre

end ProjectionOrdered
end JSP000404Research
