import JSP000404Research.ResidualQTTTAntipodeTerminal
import Mathlib.Tactic

/-!
# The Q/T/T/T antipode blocker is the common owner or a fresh vertex

If the retained colour common to all four Q/T/T/T vertices is cx, then the
triple owner-coordinate antipode cannot be a completion word at s, y, or z.
Thus any completion blocker is either x, the translated owner corresponding
to the common colour, or a fresh vertex.  The cy and cz cases are symmetric.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem QTTT_common_colour_tripleAntipode_blocker_common_owner_or_fresh
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s x y z : V}
    {word : Fin n → Bool}
    {cx cy cz d : Fin n}
    (hcxy : cx ≠ cy) (hcxz : cx ≠ cz) (hcyz : cy ≠ cz)
    (hsActive : retainedActive C s = {cx,cy,cz})
    (hcommonS : d ∈ retainedActive C s)
    (hcommonX : d ∈ retainedActive C x)
    (hcommonY : d ∈ retainedActive C y)
    (hcommonZ : d ∈ retainedActive C z)
    (hsQ : word ∈ retainedCompletionWords C s)
    (hxT : word ∈ translatedCompletionWords C x cx)
    (hyT : word ∈ translatedCompletionWords C y cy)
    (hzT : word ∈ translatedCompletionWords C z cz) :
    let anti := tripleFlipBoolWordN word cx cy cz
    anti ∉ coveredCompletionWords C
    ∨
    ∃ r : V,
      anti ∈ retainedCompletionWords C r ∧
      r ≠ s ∧
      (
        (d = cx ∧ r ≠ y ∧ r ≠ z) ∨
        (d = cy ∧ r ≠ x ∧ r ≠ z) ∨
        (d = cz ∧ r ≠ x ∧ r ≠ y)
      ) := by
  dsimp
  let anti := tripleFlipBoolWordN word cx cy cz
  have hcxS : cx ∈ retainedActive C s := by rw [hsActive]; simp
  have hcyS : cy ∈ retainedActive C s := by rw [hsActive]; simp
  have hczS : cz ∈ retainedActive C s := by rw [hsActive]; simp
  have hsOut : anti ∉ retainedCompletionWords C s := by
    dsimp [anti]
    exact tripleFlipBoolWordN_not_mem_completion_of_three_active
      C hcxy hcxz hcyz hcxS hcyS hczS hsQ
  have hd : d = cx ∨ d = cy ∨ d = cz := by
    rw [hsActive] at hcommonS
    simpa using hcommonS
  by_cases hhole : anti ∉ coveredCompletionWords C
  · exact Or.inl hhole
  · right
    have hcovered : anti ∈ coveredCompletionWords C := by simpa using hhole
    obtain ⟨r,hrF⟩ := (mem_coveredCompletionWords C anti).1 hcovered
    have hrQ : anti ∈ retainedCompletionWords C r :=
      (mem_completionFibre C anti r).1 hrF
    have hrs : r ≠ s := fun h => by subst r; exact hsOut hrQ
    refine ⟨r,hrQ,hrs,?_⟩
    rcases hd with hdx | hdy | hdz
    · left
      refine ⟨hdx,?_,?_⟩
      · intro hry
        subst r
        rw [hdx] at hcommonY
        exact
          (QTT_other_active_excludes_triple_antipode_completion
            C hcxy hcommonY hyT
            (tripleFlipBoolWordN_at_a word hcxy hcxz)) hrQ
      · intro hrz
        subst r
        rw [hdx] at hcommonZ
        exact
          (QTT_other_active_excludes_triple_antipode_completion
            C hcxz hcommonZ hzT
            (tripleFlipBoolWordN_at_a word hcxy hcxz)) hrQ
    · right; left
      refine ⟨hdy,?_,?_⟩
      · intro hrx
        subst r
        rw [hdy] at hcommonX
        exact
          (QTT_other_active_excludes_triple_antipode_completion
            C hcxy.symm hcommonX hxT
            (tripleFlipBoolWordN_at_b word hcxy hcyz)) hrQ
      · intro hrz
        subst r
        rw [hdy] at hcommonZ
        exact
          (QTT_other_active_excludes_triple_antipode_completion
            C hcyz hcommonZ hzT
            (tripleFlipBoolWordN_at_b word hcxy hcyz)) hrQ
    · right; right
      refine ⟨hdz,?_,?_⟩
      · intro hrx
        subst r
        rw [hdz] at hcommonX
        exact
          (QTT_other_active_excludes_triple_antipode_completion
            C hcxz.symm hcommonX hxT
            (tripleFlipBoolWordN_at_c word hcxz hcyz)) hrQ
      · intro hry
        subst r
        rw [hdz] at hcommonY
        exact
          (QTT_other_active_excludes_triple_antipode_completion
            C hcyz.symm hcommonY hyT
            (tripleFlipBoolWordN_at_c word hcxz hcyz)) hrQ

#print axioms QTTT_common_colour_tripleAntipode_blocker_common_owner_or_fresh

end OrderedEdgeColoring
end JSP000404Research
