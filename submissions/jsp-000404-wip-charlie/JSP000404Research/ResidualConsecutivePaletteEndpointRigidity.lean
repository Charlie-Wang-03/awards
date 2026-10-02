import JSP000404Research.ThreeConsecutivePaletteEndpointRigidity
import JSP000404Research.ResidualConsecutivePaletteCloseness
import Mathlib.Tactic

/-!
# Endpoint rigidity for retained consecutive palettes

If two retained palettes are both consecutive triples and contain the same two
retained colours whose labels differ by two, then the palettes are equal.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem retainedActive_eq_of_consecutive_common_distance_two
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    {mu mv : ℕ}
    (hpu :
      (retainedActive C u).map Fin.valEmbedding =
        threeNatInterval mu)
    (hpv :
      (retainedActive C v).map Fin.valEmbedding =
        threeNatInterval mv)
    {c d : Fin n}
    (hcu : c ∈ retainedActive C u)
    (hdu : d ∈ retainedActive C u)
    (hcv : c ∈ retainedActive C v)
    (hdv : d ∈ retainedActive C v)
    (hdist :
      c.val + 2 = d.val ∨ d.val + 2 = c.val) :
    retainedActive C v = retainedActive C u := by
  have hcuM :
      c.val ∈ threeNatInterval mu := by
    rw [← hpu]
    exact Finset.mem_map.mpr ⟨c,hcu,rfl⟩
  have hduM :
      d.val ∈ threeNatInterval mu := by
    rw [← hpu]
    exact Finset.mem_map.mpr ⟨d,hdu,rfl⟩
  have hcvM :
      c.val ∈ threeNatInterval mv := by
    rw [← hpv]
    exact Finset.mem_map.mpr ⟨c,hcv,rfl⟩
  have hdvM :
      d.val ∈ threeNatInterval mv := by
    rw [← hpv]
    exact Finset.mem_map.mpr ⟨d,hdv,rfl⟩
  have hstart : mv = mu :=
    threeNatInterval_start_eq_of_common_distance_two
      hcuM hduM hcvM hdvM hdist
  have hmap :
      (retainedActive C v).map Fin.valEmbedding =
        (retainedActive C u).map Fin.valEmbedding := by
    rw [hpv,hpu,hstart]
  ext q
  constructor
  · intro hq
    have hval :
        q.val ∈ (retainedActive C u).map Fin.valEmbedding := by
      rw [← hmap]
      exact Finset.mem_map.mpr ⟨q,hq,rfl⟩
    obtain ⟨q',hq',hvalEq⟩ := Finset.mem_map.mp hval
    have hqq : q' = q := by
      apply Fin.ext
      simpa using hvalEq
    simpa [hqq] using hq'
  · intro hq
    have hval :
        q.val ∈ (retainedActive C v).map Fin.valEmbedding := by
      rw [hmap]
      exact Finset.mem_map.mpr ⟨q,hq,rfl⟩
    obtain ⟨q',hq',hvalEq⟩ := Finset.mem_map.mp hval
    have hqq : q' = q := by
      apply Fin.ext
      simpa using hvalEq
    simpa [hqq] using hq'

#print axioms retainedActive_eq_of_consecutive_common_distance_two

end OrderedEdgeColoring
end JSP000404Research
