import JSP000404Research.ProjectionUnitSupportTwoConsecutiveBands
import Mathlib.Tactic

/-!
# Consecutive retained palettes give two-step colour closeness
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem retained_labels_two_step_close_of_consecutive
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V} {m : ℕ}
    (hpalette :
      (retainedActive C v).map Fin.valEmbedding =
        {m,m+1,m+2})
    {c d : Fin n}
    (hc : c ∈ retainedActive C v)
    (hd : d ∈ retainedActive C v) :
    c.val ≤ d.val + 2 ∧ d.val ≤ c.val + 2 := by
  have hcMap :
      c.val ∈ (retainedActive C v).map Fin.valEmbedding := by
    apply Finset.mem_map.mpr
    exact ⟨c,hc,rfl⟩
  have hdMap :
      d.val ∈ (retainedActive C v).map Fin.valEmbedding := by
    apply Finset.mem_map.mpr
    exact ⟨d,hd,rfl⟩
  rw [hpalette] at hcMap hdMap
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcMap hdMap
  rcases hcMap with hc0 | hc1 | hc2 <;>
    rcases hdMap with hd0 | hd1 | hd2 <;>
    omega

#print axioms retained_labels_two_step_close_of_consecutive

end OrderedEdgeColoring
end JSP000404Research
