import JSP000404Research.ResidualConsecutivePaletteEndpointRigidity
import Mathlib.Tactic

/-!
# A consecutive palette containing the middle band contains an owner endpoint
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem retainedActive_contains_endpoint_of_middle_in_consecutive
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V} {mv m : ℕ}
    (hpalette :
      (retainedActive C v).map Fin.valEmbedding =
        threeNatInterval mv)
    {mid lo hi : Fin n}
    (hmid : mid ∈ retainedActive C v)
    (hmidVal : mid.val = m + 1)
    (hloVal : lo.val = m)
    (hhiVal : hi.val = m + 2) :
    lo ∈ retainedActive C v ∨
      hi ∈ retainedActive C v := by
  have hmidMap :
      m + 1 ∈ threeNatInterval mv := by
    rw [← hpalette, ← hmidVal]
    exact Finset.mem_map.mpr ⟨mid,hmid,rfl⟩
  rcases
    threeNatInterval_containing_middle_contains_endpoint hmidMap
      with hlo | hhi
  · left
    have hloMap :
        lo.val ∈ (retainedActive C v).map Fin.valEmbedding := by
      rw [hpalette,hloVal]
      exact hlo
    obtain ⟨q,hq,hqVal⟩ := Finset.mem_map.mp hloMap
    have hqlo : q = lo := by
      apply Fin.ext
      simpa using hqVal
    simpa [hqlo] using hq
  · right
    have hhiMap :
        hi.val ∈ (retainedActive C v).map Fin.valEmbedding := by
      rw [hpalette,hhiVal]
      exact hhi
    obtain ⟨q,hq,hqVal⟩ := Finset.mem_map.mp hhiMap
    have hqhi : q = hi := by
      apply Fin.ext
      simpa using hqVal
    simpa [hqhi] using hq

#print axioms retainedActive_contains_endpoint_of_middle_in_consecutive

end OrderedEdgeColoring
end JSP000404Research
