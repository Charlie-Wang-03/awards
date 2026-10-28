import JSP000404Research.ActualAnyWidthHighExponentReuseGate
import JSP000404Research.PlanarUniqueTopExponent
import JSP000404Research.PlanarThreeFiveLossDuplicateBound
import JSP000404Research.PlanarLowerTwoGlobalCapacity
import Mathlib.Tactic

/-!
# Genuine AngleCap n=4 high-profile obstruction: reuse owners are UNIQUE TOP

The generic source-native theorem proved that any ORIGINAL loss vertex
shared by two distinct earliest-prior records charging the SAME opposite
Boolean target must have exponent >=3.

When n=4 in an ACTUAL planar AngleCap lower-branch configuration with
>=3 original centres, genuine centre exponents are <=3, and a centre
with exponent exactly n-1=3 is top-sharp and UNIQUE under AngleCap.

Thus any actual reused source owner of a four-colour translated-loss
collision must coincide with the unique geometric top exponent centre.
Neither the exterior eligibility nor global eight-source payment follows.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- In the GENUINE n=4 AngleCap standard residual colouring, if
two distinct original earliest-prior records charging one opposite
candidate share an actual original source owner v, then v is of
TOP exponent 3 and is the UNIQUE such top centre among all original
planar centres. There is no global assumption on exponents <=2. -/
theorem planar_four_colour_reused_opposite_source_is_unique_top
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
    ∀ (choice : ProjectionOrdered V → Fin 4)
      (a b : Fin 4 × Fin 4 × (Fin 4 → Bool)),
      a ∈ actualEarliestLossCollisionRecords B k choice →
      b ∈ actualEarliestLossCollisionRecords B k choice →
      a ≠ b →
      flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 =
        flipBoolWordAt (flipBoolWordAt b.2.2 b.1) b.2.1 →
      ∀ (v : ProjectionOrdered V) (c d : Fin 4),
        (c = a.1 ∨ c = a.2.1) →
        (d = b.1 ∨ d = b.2.1) →
        v ∈ lossCoordinateSlice B k choice c →
        v ∈ lossCoordinateSlice B k choice d →
        a.2.2 ∈ translatedCompletionWords B v c →
        b.2.2 ∈ translatedCompletionWords B v d →
        k v = 3 ∧
        (∀ u : ProjectionOrdered V, k u = 3 → u = v) := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have htpos : 0 < t := by rw [ht]; linarith
  have hwidth : t < (4 : ℝ) + 1 := by rw [ht]; linarith
  let D := genericDirectionData_sendov hp hcap htpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (4 + 1) :=
    standardResidualColoring D 4 (by exact_mod_cast hwidth)
  let k : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (cycles i) t
  change ∀ (choice : ProjectionOrdered V → Fin 4)
      (a b : Fin 4 × Fin 4 × (Fin 4 → Bool)),
      a ∈ actualEarliestLossCollisionRecords B k choice →
      b ∈ actualEarliestLossCollisionRecords B k choice →
      a ≠ b →
      flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 =
        flipBoolWordAt (flipBoolWordAt b.2.2 b.1) b.2.1 →
      ∀ (v : ProjectionOrdered V) (c d : Fin 4),
        (c = a.1 ∨ c = a.2.1) →
        (d = b.1 ∨ d = b.2.1) →
        v ∈ lossCoordinateSlice B k choice c →
        v ∈ lossCoordinateSlice B k choice d →
        a.2.2 ∈ translatedCompletionWords B v c →
        b.2.2 ∈ translatedCompletionWords B v d →
        k v = 3 ∧ (∀ u : ProjectionOrdered V, k u = 3 → u = v)
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
  intro choice a b ha hb hab htarget v c d hvc hud hv hu hw hz
  have hvlarge : 3 ≤ k v :=
    actual_any_width_reused_opposite_shared_owner_exponent_three
      B k choice a b ha hb hab htarget v c d hvc hud hv hu hw hz
  have hvbound : k v ≤ 3 := by
    have hk := centreExponent_lt_n
      (cycles v) 4 delta t (by decide : 1 ≤ (4 : ℕ))
      hdelta0 hdelta1 ht
    dsimp only [k]
    omega
  have hvtop : k v = 3 := by omega
  refine ⟨hvtop,?_⟩
  intro u hu
  by_contra hne
  have hvSharp : centreExponent (cycles v) t = 4 - 1 := by
    simpa only [k, Nat.reduceSub] using hvtop
  have huSharp : centreExponent (cycles u) t = 4 - 1 := by
    simpa only [k, Nat.reduceSub] using hu
  have hvne : v ≠ u := by
    intro heq
    exact hne heq.symm
  exact top_exponent_unique_of_card_ge_three
    (reindexedPoint_injective hp)
    (angleCap_reindexedPoint hp hcap)
    (by decide : 3 ≤ (4 : ℕ)) hcardRe
    hdelta0 hdeltaHalf ht hlam cycles v u hvne hvSharp huSharp

#print axioms planar_four_colour_reused_opposite_source_is_unique_top

end ProjectionOrdered
end JSP000404Research
