import JSP000404Research.ResidualLists
import Mathlib.Tactic

/-!
# Two-choice obstruction for the residual band

For the lower-half JSP-000404 route the short residual band is naturally
adjacent, on the projective direction circle, to the retained colours on its
left and right.  Recolouring a residual edge into one of these two neighbours
fails only if both candidate colours occur in the exact local forbidden list.

This file turns that failure into explicit witness edges.  It deliberately
keeps the two colours abstract; the geometric specialization will use the
first and last retained bands.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Membership in the local forbidden list is exactly an incoming witness at
the lower endpoint or an outgoing witness at the upper endpoint. -/
theorem mem_residualForbidden_iff
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1))
    (u v : V) (c : Fin k) :
    c ∈ residualForbidden C u v ↔
      (∃ a, a < u ∧ C.color a u = c.castSucc) ∨
      (∃ w, v < w ∧ C.color v w = c.castSucc) := by
  classical
  simp [residualForbidden, mem_incomingRetained_iff,
    mem_outgoingRetained_iff]

/-- A candidate colour outside the forbidden list is a valid local target. -/
theorem candidate_compatible_of_not_forbidden
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1))
    {u v : V} {c : Fin k}
    (hc : c ∉ residualForbidden C u v) :
    (∀ {a : V} (hau : a < u)
        (haRet : (C.color a u).val < k),
      c ≠ retainedColor C a u haRet) ∧
    (∀ {w : V} (hvw : v < w)
        (hwRet : (C.color v w).val < k),
      c ≠ retainedColor C v w hwRet) :=
  compatible_target_of_not_mem_forbidden C c hc

/-- Either one of two proposed colours is locally safe, or both colours have
explicit forbidden-list witnesses. -/
theorem two_choice_safe_or_obstructed
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1))
    (u v : V) (left right : Fin k) :
    (left ∉ residualForbidden C u v) ∨
    (right ∉ residualForbidden C u v) ∨
    ((∃ a, a < u ∧ C.color a u = left.castSucc) ∨
       (∃ w, v < w ∧ C.color v w = left.castSucc)) ∧
     ((∃ a, a < u ∧ C.color a u = right.castSucc) ∨
       (∃ w, v < w ∧ C.color v w = right.castSucc)) := by
  classical
  by_cases hleft : left ∈ residualForbidden C u v
  · by_cases hright : right ∈ residualForbidden C u v
    · exact Or.inr <| Or.inr ⟨
        (mem_residualForbidden_iff C u v left).1 hleft,
        (mem_residualForbidden_iff C u v right).1 hright⟩
    · exact Or.inr <| Or.inl hright
  · exact Or.inl hleft

/-- If both neighbouring candidates are forbidden, the obstruction splits
into exactly four side combinations. -/
theorem two_choice_four_obstruction_cases
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1))
    {u v : V} {left right : Fin k}
    (hleft : left ∈ residualForbidden C u v)
    (hright : right ∈ residualForbidden C u v) :
    ( (∃ aL aR, aL < u ∧ aR < u ∧
          C.color aL u = left.castSucc ∧
          C.color aR u = right.castSucc) ) ∨
    ( (∃ aL wR, aL < u ∧ v < wR ∧
          C.color aL u = left.castSucc ∧
          C.color v wR = right.castSucc) ) ∨
    ( (∃ wL aR, v < wL ∧ aR < u ∧
          C.color v wL = left.castSucc ∧
          C.color aR u = right.castSucc) ) ∨
    ( (∃ wL wR, v < wL ∧ v < wR ∧
          C.color v wL = left.castSucc ∧
          C.color v wR = right.castSucc) ) := by
  rcases (mem_residualForbidden_iff C u v left).1 hleft with hLi | hLo
  · rcases (mem_residualForbidden_iff C u v right).1 hright with hRi | hRo
    · rcases hLi with ⟨aL, haL, hcL⟩
      rcases hRi with ⟨aR, haR, hcR⟩
      exact Or.inl ⟨aL, aR, haL, haR, hcL, hcR⟩
    · rcases hLi with ⟨aL, haL, hcL⟩
      rcases hRo with ⟨wR, hwR, hcR⟩
      exact Or.inr <| Or.inl ⟨aL, wR, haL, hwR, hcL, hcR⟩
  · rcases (mem_residualForbidden_iff C u v right).1 hright with hRi | hRo
    · rcases hLo with ⟨wL, hwL, hcL⟩
      rcases hRi with ⟨aR, haR, hcR⟩
      exact Or.inr <| Or.inr <| Or.inl
        ⟨wL, aR, hwL, haR, hcL, hcR⟩
    · rcases hLo with ⟨wL, hwL, hcL⟩
      rcases hRo with ⟨wR, hwR, hcR⟩
      exact Or.inr <| Or.inr <| Or.inr
        ⟨wL, wR, hwL, hwR, hcL, hcR⟩

#print axioms mem_residualForbidden_iff
#print axioms candidate_compatible_of_not_forbidden
#print axioms two_choice_safe_or_obstructed
#print axioms two_choice_four_obstruction_cases

end OrderedEdgeColoring
end JSP000404Research
