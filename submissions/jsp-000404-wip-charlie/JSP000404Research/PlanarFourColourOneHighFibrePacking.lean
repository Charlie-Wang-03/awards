import JSP000404Research.PlanarFourColourHighLossReuseUniqueTop
import JSP000404Research.ActualOneHighLossCentreFibrePacking
import Mathlib.Tactic

/-!
# Actual planar n=4 source-native fibre packing with one possible top

For lower-branch AngleCap and >=3 genuine original planar centres,
the top exponent n-1=3 occurs at most ONCE. All actual original
exponents are <=3; therefore at most one projected-loss centre can
have exponent >=3.

The arbitrary-n mixed-profile fibre injection gives, for every TRUE
original source collision target q, an injection into the genuine
projected-loss centres of exponent <=2. A repeated source target cannot
claim a low exponent centre twice. This gives direct AngleCap evidence
without asserting that q is an exterior Boolean hole.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- For the ACTUAL n=4 planar AngleCap standard residual colouring,
each genuine earliest-prior opposite-target source fibre injects into
the original projected-loss centres with exponent <=2. No globally
imposed k<=2; the only high k=3 top centre, if present, is unique
by genuine AngleCap sharpness. -/
theorem planar_four_colour_opposite_fibre_le_low_loss_centres
    {V : Type*} [Fintype V]
    {p : V → Plane}
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
    ∀ (choice : ProjectionOrdered V → Fin 4) (q : Fin 4 → Bool),
      (actualLossOppositeCandidateFibre B k choice q).card ≤
        ((projectedLossVertices B k).filter (fun i => k i ≤ 2)).card := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have htpos : 0 < t := by rw [ht]; linarith
  have hwidth : t < (4 : ℝ) + 1 := by rw [ht]; linarith
  let D := genericDirectionData_sendov hp hcap htpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (4 + 1) :=
    standardResidualColoring D 4 (by exact_mod_cast hwidth)
  let k : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (cycles i) t
  change ∀ (choice : ProjectionOrdered V → Fin 4) (q : Fin 4 → Bool),
      (actualLossOppositeCandidateFibre B k choice q).card ≤
        ((projectedLossVertices B k).filter (fun i => k i ≤ 2)).card
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
  have hk (v : ProjectionOrdered V) : k v ≤ 3 := by
    have h := centreExponent_lt_n
      (cycles v) 4 delta t (by decide : 1 ≤ (4 : ℕ))
      hdelta0 hdelta1 ht
    dsimp [k]
    omega
  have htop :
      ((Finset.univ : Finset (ProjectionOrdered V)).filter
        (fun v => centreExponent (cycles v) t = 4 - 1)).card ≤ 1 :=
    actual_top_exponent_layer_card_le_one
      (reindexedPoint_injective hp)
      (angleCap_reindexedPoint hp hcap)
      (by decide : 3 ≤ (4 : ℕ)) hcardRe
      hdelta0 hdeltaHalf ht hlam cycles
  have hsub :
      ((projectedLossVertices B k).filter (fun v => 3 ≤ k v)) ⊆
      ((Finset.univ : Finset (ProjectionOrdered V)).filter
        (fun v => centreExponent (cycles v) t = 4 - 1)) := by
    intro v hv
    have hge := (Finset.mem_filter.mp hv).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    have hb := hk v
    dsimp only [k] at hge hb
    omega
  have hhigh :
      ((projectedLossVertices B k).filter
        (fun v => 3 ≤ k v)).card ≤ 1 :=
    (Finset.card_le_card hsub).trans htop
  intro choice q
  exact actual_one_high_loss_centre_opposite_fibre_le_low_centres
    B k choice hhigh q

#print axioms planar_four_colour_opposite_fibre_le_low_loss_centres

end ProjectionOrdered
end JSP000404Research
