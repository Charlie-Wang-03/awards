import JSP000404Research.ResidualOverlapDimension
import Mathlib.Tactic

/-!
# Symmetry of the common-inactive retained palette
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem commonInactiveRetained_comm
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) :
    commonInactiveRetained C u v =
      commonInactiveRetained C v u := by
  classical
  ext c
  simp only [mem_commonInactiveRetained]
  constructor
  · rintro ⟨hu,hv⟩
    exact ⟨hv,hu⟩
  · rintro ⟨hv,hu⟩
    exact ⟨hu,hv⟩

theorem commonInactiveRetained_card_comm
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) :
    (commonInactiveRetained C u v).card =
      (commonInactiveRetained C v u).card := by
  rw [commonInactiveRetained_comm C u v]

#print axioms commonInactiveRetained_comm
#print axioms commonInactiveRetained_card_comm

end OrderedEdgeColoring
end JSP000404Research
