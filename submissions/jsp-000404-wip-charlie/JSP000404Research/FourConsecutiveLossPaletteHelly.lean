import JSP000404Research.ThreeColourPaletteHelly
import JSP000404Research.ResidualLossBlockerEdge
import JSP000404Research.ResidualLossFibreEdgeClassification
import JSP000404Research.ResidualLossDirectionalWitness
import Mathlib.Tactic

/-!
# Common retained colour for four consecutive loss palettes

Any two distinct projected-loss vertices are joined by a retained edge, whose
retained colour belongs to both endpoint retained palettes.

Hence four pairwise distinct projected-loss vertices have pairwise-intersecting
retained palettes.  If each palette is exactly three consecutive integer
labels, the discrete Helly lemma forces one retained coordinate to be active
at all four vertices.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem projectedLoss_pair_retainedActive_inter_nonempty
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {x y : V}
    (hxy : x ≠ y)
    (hxLoss : x ∈ projectedLossVertices C exponent)
    (hyLoss : y ∈ projectedLossVertices C exponent) :
    (retainedActive C x ∩ retainedActive C y).Nonempty := by
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · have hret :=
      projectedLoss_edge_right_retained
        C exponent hexp honeLoss hxLoss hlt
    let e := retainedColor C x y hret
    refine ⟨e,?_,?_⟩
    · exact retainedColor_mem_retainedActive_left C hlt hret
    · exact retainedColor_mem_retainedActive_right C hlt hret
  · have hret :=
      projectedLoss_edge_right_retained
        C exponent hexp honeLoss hyLoss hgt
    let e := retainedColor C y x hret
    refine ⟨e,?_,?_⟩
    · exact retainedColor_mem_retainedActive_right C hgt hret
    · exact retainedColor_mem_retainedActive_left C hgt hret

theorem mapped_palette_intersection_of_retained_intersection
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {x y : V} {mx my : ℕ}
    (hpx :
      (retainedActive C x).map Fin.valEmbedding =
        threeNatInterval mx)
    (hpy :
      (retainedActive C y).map Fin.valEmbedding =
        threeNatInterval my)
    (hinter :
      (retainedActive C x ∩ retainedActive C y).Nonempty) :
    (threeNatInterval mx ∩ threeNatInterval my).Nonempty := by
  obtain ⟨c,hc⟩ := hinter
  have ⟨hcx,hcy⟩ := Finset.mem_inter.mp hc
  refine ⟨c.val,?_,?_⟩
  · rw [← hpx]
    exact Finset.mem_map.mpr ⟨c,hcx,rfl⟩
  · rw [← hpy]
    exact Finset.mem_map.mpr ⟨c,hcy,rfl⟩

theorem four_projectedLoss_consecutive_palettes_common_retained
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (haLoss : a ∈ projectedLossVertices C exponent)
    (hbLoss : b ∈ projectedLossVertices C exponent)
    (hcLoss : c ∈ projectedLossVertices C exponent)
    (hdLoss : d ∈ projectedLossVertices C exponent)
    {ma mb mc md : ℕ}
    (hpa :
      (retainedActive C a).map Fin.valEmbedding =
        threeNatInterval ma)
    (hpb :
      (retainedActive C b).map Fin.valEmbedding =
        threeNatInterval mb)
    (hpc :
      (retainedActive C c).map Fin.valEmbedding =
        threeNatInterval mc)
    (hpd :
      (retainedActive C d).map Fin.valEmbedding =
        threeNatInterval md) :
    ∃ color : Fin n,
      color ∈ retainedActive C a ∧
      color ∈ retainedActive C b ∧
      color ∈ retainedActive C c ∧
      color ∈ retainedActive C d := by
  have habI :=
    mapped_palette_intersection_of_retained_intersection
      C hpa hpb
      (projectedLoss_pair_retainedActive_inter_nonempty
        C exponent hexp honeLoss hab haLoss hbLoss)
  have hacI :=
    mapped_palette_intersection_of_retained_intersection
      C hpa hpc
      (projectedLoss_pair_retainedActive_inter_nonempty
        C exponent hexp honeLoss hac haLoss hcLoss)
  have hadI :=
    mapped_palette_intersection_of_retained_intersection
      C hpa hpd
      (projectedLoss_pair_retainedActive_inter_nonempty
        C exponent hexp honeLoss had haLoss hdLoss)
  have hbcI :=
    mapped_palette_intersection_of_retained_intersection
      C hpb hpc
      (projectedLoss_pair_retainedActive_inter_nonempty
        C exponent hexp honeLoss hbc hbLoss hcLoss)
  have hbdI :=
    mapped_palette_intersection_of_retained_intersection
      C hpb hpd
      (projectedLoss_pair_retainedActive_inter_nonempty
        C exponent hexp honeLoss hbd hbLoss hdLoss)
  have hcdI :=
    mapped_palette_intersection_of_retained_intersection
      C hpc hpd
      (projectedLoss_pair_retainedActive_inter_nonempty
        C exponent hexp honeLoss hcd hcLoss hdLoss)

  obtain ⟨k,hka,hkb,hkc,hkd⟩ :=
    four_threeNatIntervals_pairwise_intersect_common
      habI hacI hadI hbcI hbdI hcdI

  have hkaMap :
      k ∈ (retainedActive C a).map Fin.valEmbedding := by
    rw [hpa]
    exact hka
  obtain ⟨ca,hcaActive,hcaVal⟩ := Finset.mem_map.mp hkaMap

  have hkbMap :
      k ∈ (retainedActive C b).map Fin.valEmbedding := by
    rw [hpb]
    exact hkb
  obtain ⟨cb,hcbActive,hcbVal⟩ := Finset.mem_map.mp hkbMap

  have hkcMap :
      k ∈ (retainedActive C c).map Fin.valEmbedding := by
    rw [hpc]
    exact hkc
  obtain ⟨cc,hccActive,hccVal⟩ := Finset.mem_map.mp hkcMap

  have hkdMap :
      k ∈ (retainedActive C d).map Fin.valEmbedding := by
    rw [hpd]
    exact hkd
  obtain ⟨cd,hcdActive,hcdVal⟩ := Finset.mem_map.mp hkdMap

  have habColor : ca = cb := by
    apply Fin.ext
    have haVal : ca.val = k := by simpa using hcaVal
    have hbVal : cb.val = k := by simpa using hcbVal
    omega
  have hacColor : ca = cc := by
    apply Fin.ext
    have haVal : ca.val = k := by simpa using hcaVal
    have hcVal : cc.val = k := by simpa using hccVal
    omega
  have hadColor : ca = cd := by
    apply Fin.ext
    have haVal : ca.val = k := by simpa using hcaVal
    have hdVal : cd.val = k := by simpa using hcdVal
    omega

  refine ⟨ca,hcaActive,?_,?_,?_⟩
  · simpa [habColor] using hcbActive
  · simpa [hacColor] using hccActive
  · simpa [hadColor] using hcdActive

#print axioms projectedLoss_pair_retainedActive_inter_nonempty
#print axioms four_projectedLoss_consecutive_palettes_common_retained

end OrderedEdgeColoring
end JSP000404Research
