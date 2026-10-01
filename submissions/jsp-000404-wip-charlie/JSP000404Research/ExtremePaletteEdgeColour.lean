import JSP000404Research.FourConsecutiveLossPaletteHelly
import JSP000404Research.ResidualLossDirectionalWitness
import Mathlib.Tactic

/-!
# Edge colour forced by extreme consecutive palettes

Two consecutive three-colour palettes with starts m and m+2 intersect in the
single label m+2.  For two projected-loss vertices carrying those palettes,
their joining retained edge colour belongs to both endpoint palettes, hence is
forced to be exactly m+2.
-/

namespace JSP000404Research

theorem threeNatInterval_extreme_inter_eq_singleton
    (m : ℕ) :
    threeNatInterval m ∩ threeNatInterval (m + 2)
      = {m + 2} := by
  ext k
  rw [Finset.mem_inter, Finset.mem_singleton]
  rw [mem_threeNatInterval_iff_bounds,
      mem_threeNatInterval_iff_bounds]
  omega

namespace OrderedEdgeColoring

theorem projectedLoss_edge_colour_forced_of_extreme_three_palettes
    {V : Type*} [LinearOrder V] [Fintype V] {n m : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {u v : V}
    (huv : u < v)
    (huLoss : u ∈ projectedLossVertices C exponent)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (huPal :
      (retainedActive C u).map Fin.valEmbedding =
        threeNatInterval m)
    (hvPal :
      (retainedActive C v).map Fin.valEmbedding =
        threeNatInterval (m + 2)) :
    ∃ hret : (C.color u v).val < n,
      (retainedColor C u v hret).val = m + 2 := by
  have hret :
      (C.color u v).val < n :=
    projectedLoss_edge_right_retained
      C exponent hexp honeLoss huLoss huv
  let e : Fin n := retainedColor C u v hret
  have heu : e ∈ retainedActive C u :=
    retainedColor_mem_retainedActive_left C huv hret
  have hev : e ∈ retainedActive C v :=
    retainedColor_mem_retainedActive_right C huv hret
  have heuMap :
      e.val ∈ threeNatInterval m := by
    rw [← huPal]
    exact Finset.mem_map.mpr ⟨e,heu,rfl⟩
  have hevMap :
      e.val ∈ threeNatInterval (m+2) := by
    rw [← hvPal]
    exact Finset.mem_map.mpr ⟨e,hev,rfl⟩
  have hinter :
      e.val ∈
        threeNatInterval m ∩ threeNatInterval (m+2) :=
    Finset.mem_inter.mpr ⟨heuMap,hevMap⟩
  rw [threeNatInterval_extreme_inter_eq_singleton] at hinter
  have heq : e.val = m + 2 := by simpa using hinter
  exact ⟨hret,heq⟩

theorem projectedLoss_edge_colour_forced_of_extreme_three_palettes_rev
    {V : Type*} [LinearOrder V] [Fintype V] {n m : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {u v : V}
    (huv : u < v)
    (huLoss : u ∈ projectedLossVertices C exponent)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (huPal :
      (retainedActive C u).map Fin.valEmbedding =
        threeNatInterval (m + 2))
    (hvPal :
      (retainedActive C v).map Fin.valEmbedding =
        threeNatInterval m) :
    ∃ hret : (C.color u v).val < n,
      (retainedColor C u v hret).val = m + 2 := by
  have hret :
      (C.color u v).val < n :=
    projectedLoss_edge_right_retained
      C exponent hexp honeLoss huLoss huv
  let e : Fin n := retainedColor C u v hret
  have heu : e ∈ retainedActive C u :=
    retainedColor_mem_retainedActive_left C huv hret
  have hev : e ∈ retainedActive C v :=
    retainedColor_mem_retainedActive_right C huv hret
  have heuMap :
      e.val ∈ threeNatInterval (m+2) := by
    rw [← huPal]
    exact Finset.mem_map.mpr ⟨e,heu,rfl⟩
  have hevMap :
      e.val ∈ threeNatInterval m := by
    rw [← hvPal]
    exact Finset.mem_map.mpr ⟨e,hev,rfl⟩
  have hinter :
      e.val ∈
        threeNatInterval m ∩ threeNatInterval (m+2) :=
    Finset.mem_inter.mpr ⟨hevMap,heuMap⟩
  rw [threeNatInterval_extreme_inter_eq_singleton] at hinter
  have heq : e.val = m + 2 := by simpa using hinter
  exact ⟨hret,heq⟩

#print axioms threeNatInterval_extreme_inter_eq_singleton
#print axioms projectedLoss_edge_colour_forced_of_extreme_three_palettes
#print axioms projectedLoss_edge_colour_forced_of_extreme_three_palettes_rev

end OrderedEdgeColoring
end JSP000404Research
