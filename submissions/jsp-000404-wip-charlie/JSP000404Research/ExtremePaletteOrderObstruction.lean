import JSP000404Research.ExtremePaletteEdgeColour
import Mathlib.Tactic

/-!
# Order obstruction for the two extreme palette classes

If every edge joining a vertex of class L to a vertex of class R has one fixed
colour, admissibility forbids an alternating ordered triple L-R-L or R-L-R.
Thus, along the ambient linear order, the two extreme classes can switch at
most once.

This is the order-theoretic terminal produced when consecutive three-colour
palette starts have full spread two.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem no_extreme_palette_alternation_LRL
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a b c : V}
    (hab : a < b)
    (hbc : b < c)
    {e : Fin n}
    (habRet : (C.color a b).val < n)
    (hbcRet : (C.color b c).val < n)
    (habCol : retainedColor C a b habRet = e)
    (hbcCol : retainedColor C b c hbcRet = e) :
    False := by
  have habFull :
      C.color a b = e.castSucc := by
    apply Fin.ext
    have h := congrArg Fin.val habCol
    simpa [retainedColor] using h
  have hbcFull :
      C.color b c = e.castSucc := by
    apply Fin.ext
    have h := congrArg Fin.val hbcCol
    simpa [retainedColor] using h
  exact C.noMonoTwoPath hab hbc (by rw [habFull,hbcFull])

theorem no_three_ordered_vertices_with_extreme_palette_pattern
    {V : Type*} [LinearOrder V] [Fintype V]
    {n m : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {a b c : V}
    (hab : a < b)
    (hbc : b < c)
    (haLoss : a ∈ projectedLossVertices C exponent)
    (hbLoss : b ∈ projectedLossVertices C exponent)
    (hcLoss : c ∈ projectedLossVertices C exponent)
    (haPal :
      (retainedActive C a).map Fin.valEmbedding =
        threeNatInterval m)
    (hbPal :
      (retainedActive C b).map Fin.valEmbedding =
        threeNatInterval (m+2))
    (hcPal :
      (retainedActive C c).map Fin.valEmbedding =
        threeNatInterval m) :
    False := by
  obtain ⟨habRet,habVal⟩ :=
    projectedLoss_edge_colour_forced_of_extreme_three_palettes
      C exponent hexp honeLoss
      hab haLoss hbLoss haPal hbPal
  obtain ⟨hbcRet,hbcVal⟩ :=
    projectedLoss_edge_colour_forced_of_extreme_three_palettes_rev
      C exponent hexp honeLoss
      hbc hbLoss hcLoss hbPal hcPal
  let e : Fin n := retainedColor C a b habRet
  have heq :
      retainedColor C b c hbcRet = e := by
    apply Fin.ext
    have h1 : (retainedColor C a b habRet).val = m+2 := habVal
    have h2 : (retainedColor C b c hbcRet).val = m+2 := hbcVal
    simpa [e] using h2.trans h1.symm
  exact no_extreme_palette_alternation_LRL
    C hab hbc habRet hbcRet rfl heq

theorem no_three_ordered_vertices_with_extreme_palette_pattern_rev
    {V : Type*} [LinearOrder V] [Fintype V]
    {n m : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {a b c : V}
    (hab : a < b)
    (hbc : b < c)
    (haLoss : a ∈ projectedLossVertices C exponent)
    (hbLoss : b ∈ projectedLossVertices C exponent)
    (hcLoss : c ∈ projectedLossVertices C exponent)
    (haPal :
      (retainedActive C a).map Fin.valEmbedding =
        threeNatInterval (m+2))
    (hbPal :
      (retainedActive C b).map Fin.valEmbedding =
        threeNatInterval m)
    (hcPal :
      (retainedActive C c).map Fin.valEmbedding =
        threeNatInterval (m+2)) :
    False := by
  obtain ⟨habRet,habVal⟩ :=
    projectedLoss_edge_colour_forced_of_extreme_three_palettes_rev
      C exponent hexp honeLoss
      hab haLoss hbLoss haPal hbPal
  obtain ⟨hbcRet,hbcVal⟩ :=
    projectedLoss_edge_colour_forced_of_extreme_three_palettes
      C exponent hexp honeLoss
      hbc hbLoss hcLoss hbPal hcPal
  let e : Fin n := retainedColor C a b habRet
  have heq :
      retainedColor C b c hbcRet = e := by
    apply Fin.ext
    have h1 : (retainedColor C a b habRet).val = m+2 := habVal
    have h2 : (retainedColor C b c hbcRet).val = m+2 := hbcVal
    simpa [e] using h2.trans h1.symm
  exact no_extreme_palette_alternation_LRL
    C hab hbc habRet hbcRet rfl heq

#print axioms no_extreme_palette_alternation_LRL
#print axioms no_three_ordered_vertices_with_extreme_palette_pattern
#print axioms no_three_ordered_vertices_with_extreme_palette_pattern_rev

end OrderedEdgeColoring
end JSP000404Research
