import JSP000404Research.OrderedDirections
import Mathlib.Tactic

/-!
# Restricting ordered direction data

Every subset of a counterexample inherits the same normalized direction width
and all ordered-direction axioms.  This is the formal shell behind the
minimal-cardinality reduction used in the lower branch: once the geometric
capacity theorem is proved for a critical subconfiguration, larger
counterexamples may be cut down without changing the angle cap.

The module deliberately keeps subset selection separate; the important point
here is that no direction-data axiom is lost under restriction.
-/

namespace JSP000404Research
namespace DirectionData

/-- Restrict ordered direction data to an arbitrary subtype. -/
def restrict
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width)
    (P : V → Prop) :
    DirectionData {v : V // P v} width where
  value := fun i j => D.value i.1 j.1
  nonnegative := by
    intro i j hij
    exact D.nonnegative hij
  belowWidth := by
    intro i j hij
    exact D.belowWidth hij
  between := by
    intro i j k hij hjk
    exact D.between hij hjk
  middleSeparated := by
    intro i j k hij hjk
    exact D.middleSeparated hij hjk
  firstGap := by
    intro i j k hij hjk
    exact D.firstGap hij hjk
  lastGap := by
    intro i j k hij hjk
    exact D.lastGap hij hjk

/-- Finset-specialized restriction, convenient for finite critical
subconfigurations. -/
def restrictFinset
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width)
    (S : Finset V) :
    DirectionData {v : V // v ∈ S} width :=
  D.restrict (fun v => v ∈ S)

@[simp] theorem restrict_value
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width)
    (P : V → Prop)
    (i j : {v : V // P v}) :
    (D.restrict P).value i j = D.value i.1 j.1 := rfl

#print axioms restrict
#print axioms restrictFinset

end DirectionData
end JSP000404Research
