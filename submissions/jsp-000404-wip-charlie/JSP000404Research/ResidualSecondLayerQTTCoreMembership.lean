import JSP000404Research.ResidualSecondLayerQTTSourcePreserving
import Mathlib.Tactic

/-!
# Core-membership preserving Q/T/T/T saturation

This is the finite-set wrapper needed by minimal-core arguments.  If the
three original second-layer carriers are vertices of a core T, then the two
translated owners produced by canonicalization remain in T.  The completion
owner and the fresh third-exit blocker are not asserted to lie in T.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem mem_core_of_mem_three_values
    {V : Type*} [DecidableEq V]
    {T : Finset V}
    {u v w : {q : V // q ∈ T}}
    {x : V}
    (hx : x ∈ ({u.1,v.1,w.1} : Finset V)) :
    x ∈ T := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact u.2
  · exact v.2
  · exact w.2

theorem core_threeSecond_commonWord_QTTT_or_closed
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ z, exponent z < n)
    (hexp : ∀ z, exponent z ≤ n)
    (honeLoss :
      ∀ z, (active C z).card ≤ n - exponent z + 1)
    {T : Finset V}
    {u v w : {q : V // q ∈ T}}
    (huv : u ≠ v)
    (huw : u ≠ w)
    (hvw : v ≠ w)
    (huLoss : u.1 ∈ projectedLossVertices C exponent)
    (hvLoss : v.1 ∈ projectedLossVertices C exponent)
    (hwLoss : w.1 ∈ projectedLossVertices C exponent)
    (huSecond : exponent u.1 = n - 2)
    (hvSecond : exponent v.1 = n - 2)
    (hwSecond : exponent w.1 = n - 2)
    {word : Fin n → Bool}
    (huBlock :
      word ∈ enlargedProjectedCandidateBlock C exponent u.1)
    (hvBlock :
      word ∈ enlargedProjectedCandidateBlock C exponent v.1)
    (hwBlock :
      word ∈ enlargedProjectedCandidateBlock C exponent w.1) :
    (
      ∃ hole : Fin n → Bool,
        hole ∉ coveredCompletionWords C
    )
    ∨
    (
      ∃ q : V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree C) q
    )
    ∨
    (
      ∃ q : V,
        ExactProjectedBudget C exponent q
    )
    ∨
    (
      ∃ q : V,
        q ∈ projectedLossVertices C exponent ∧
        exponent q = n - 1
    )
    ∨
    (
      ∃ q : V,
        q ∈ projectedLossVertices C exponent ∧
        exponent q + 3 ≤ n
    )
    ∨
    (
      ∃ s x y z : V,
      ∃ cx cy cz : Fin n,
        s ≠ x ∧ s ≠ y ∧ s ≠ z ∧
        x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
        x ∈ T ∧ y ∈ T ∧
        s ∈ projectedLossVertices C exponent ∧
        x ∈ projectedLossVertices C exponent ∧
        y ∈ projectedLossVertices C exponent ∧
        z ∈ projectedLossVertices C exponent ∧
        exponent s = n - 2 ∧
        exponent x = n - 2 ∧
        exponent y = n - 2 ∧
        exponent z = n - 2 ∧
        cx ∈ retainedActive C x ∧
        cy ∈ retainedActive C y ∧
        cz ∈ retainedActive C z ∧
        cx ≠ cy ∧ cx ≠ cz ∧ cy ≠ cz ∧
        retainedActive C s = {cx,cy,cz} ∧
        word ∈ retainedCompletionWords C s ∧
        word ∈ translatedCompletionWords C x cx ∧
        word ∈ translatedCompletionWords C y cy ∧
        word ∈ translatedCompletionWords C z cz
    ) := by
  have huvVal : u.1 ≠ v.1 := by
    intro h
    apply huv
    exact Subtype.ext h
  have huwVal : u.1 ≠ w.1 := by
    intro h
    apply huw
    exact Subtype.ext h
  have hvwVal : v.1 ≠ w.1 := by
    intro h
    apply hvw
    exact Subtype.ext h

  rcases
    threeSecond_commonWord_QTTT_or_closed_with_sources
      C exponent hexpLt hexp honeLoss
      huvVal huwVal hvwVal
      huLoss hvLoss hwLoss
      huSecond hvSecond hwSecond
      huBlock hvBlock hwBlock
    with hhole | hpaid | hexact | htop | hdeep | hQTTT
  · exact Or.inl hhole
  · exact Or.inr (Or.inl hpaid)
  · exact Or.inr (Or.inr (Or.inl hexact))
  · exact Or.inr (Or.inr (Or.inr (Or.inl htop)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep))))
  · obtain ⟨s,x,y,z,cx,cy,cz,
      hsx,hsy,hsz,hxy,hxz,hyz,
      hxSource,hySource,
      hsLoss,hxLoss,hyLoss,hzLoss,
      hsSecond,hxSecond,hySecond,hzSecond,
      hcx,hcy,hcz,hcxy,hcxz,hcyz,
      hsActive,hsQ,hxT,hyT,hzT⟩ := hQTTT
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨s,x,y,z,cx,cy,cz,
        hsx,hsy,hsz,hxy,hxz,hyz,
        mem_core_of_mem_three_values hxSource,
        mem_core_of_mem_three_values hySource,
        hsLoss,hxLoss,hyLoss,hzLoss,
        hsSecond,hxSecond,hySecond,hzSecond,
        hcx,hcy,hcz,hcxy,hcxz,hcyz,
        hsActive,hsQ,hxT,hyT,hzT⟩))))

#print axioms core_threeSecond_commonWord_QTTT_or_closed

end OrderedEdgeColoring
end JSP000404Research
