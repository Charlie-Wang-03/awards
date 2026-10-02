import JSP000404Research.ResidualConsecutivePaletteMiddleEndpoint
import JSP000404Research.ResidualThreeCoordinateAntipode
import Mathlib.Tactic

/-!
# Middle common owner cannot block the Q/T/T/T antipode

A translated owner whose owner coordinate is the middle label m+1 of the
three owner bands has a consecutive retained palette.  Any consecutive triple
containing m+1 contains m or m+2.  The triple owner-coordinate antipode flips
both endpoint bits relative to the translated owner's completion base, hence
cannot lie in that completion cube.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem middle_owner_consecutive_excludes_target_completion
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V} {word target : Fin n → Bool}
    {owner lo hi : Fin n}
    {mv m : ℕ}
    (hpalette :
      (retainedActive C v).map Fin.valEmbedding =
        threeNatInterval mv)
    (howner : owner ∈ retainedActive C v)
    (hownerVal : owner.val = m + 1)
    (hloVal : lo.val = m)
    (hhiVal : hi.val = m + 2)
    (hloOwner : lo ≠ owner)
    (hhiOwner : hi ≠ owner)
    (hvT : word ∈ translatedCompletionWords C v owner)
    (htargetLo : target lo = !(word lo))
    (htargetHi : target hi = !(word hi)) :
    target ∉ retainedCompletionWords C v := by
  have hend :
      lo ∈ retainedActive C v ∨ hi ∈ retainedActive C v :=
    retainedActive_contains_endpoint_of_middle_in_consecutive
      C hpalette howner hownerVal hloVal hhiVal
  intro htarget
  have hbase :
      flipBoolWordAt word owner ∈ retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v owner word).1 hvT
  rcases hend with hlo | hhi
  · have hbaseFix :=
      (mem_retainedCompletionWords C v
        (flipBoolWordAt word owner)).1 hbase lo hlo
    have htargetFix :=
      (mem_retainedCompletionWords C v target).1 htarget lo hlo
    rw [flipBoolWordAt_off word hloOwner,
        htargetLo, hbaseFix] at htargetFix
    cases h : retainedBit C v lo <;> simp [h] at htargetFix
  · have hbaseFix :=
      (mem_retainedCompletionWords C v
        (flipBoolWordAt word owner)).1 hbase hi hhi
    have htargetFix :=
      (mem_retainedCompletionWords C v target).1 htarget hi hhi
    rw [flipBoolWordAt_off word hhiOwner,
        htargetHi, hbaseFix] at htargetFix
    cases h : retainedBit C v hi <;> simp [h] at htargetFix

theorem two_other_owner_values_are_endpoints_of_middle
    {n : ℕ}
    {cx cy cz : Fin n}
    {m : ℕ}
    (hcxy : cx ≠ cy) (hcxz : cx ≠ cz) (hcyz : cy ≠ cz)
    (hcx : cx.val ∈ threeNatInterval m)
    (hcy : cy.val ∈ threeNatInterval m)
    (hcz : cz.val ∈ threeNatInterval m)
    (hmid : cx.val = m + 1) :
    (cy.val = m ∧ cz.val = m + 2) ∨
    (cz.val = m ∧ cy.val = m + 2) := by
  have hcxB := mem_threeNatInterval_iff_bounds.mp hcx
  have hcyB := mem_threeNatInterval_iff_bounds.mp hcy
  have hczB := mem_threeNatInterval_iff_bounds.mp hcz
  have hxyVal : cx.val ≠ cy.val := by
    intro h
    exact hcxy (Fin.ext h)
  have hxzVal : cx.val ≠ cz.val := by
    intro h
    exact hcxz (Fin.ext h)
  have hyzVal : cy.val ≠ cz.val := by
    intro h
    exact hcyz (Fin.ext h)
  omega

#print axioms middle_owner_consecutive_excludes_target_completion
#print axioms two_other_owner_values_are_endpoints_of_middle

end OrderedEdgeColoring
end JSP000404Research
