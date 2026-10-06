import JSP000404Research.ResidualLossDirectionalWitness
import JSP000404Research.RetainedOrientation
import Mathlib.Tactic

/-!
# Uniqueness of a projected-loss whole-cube partner at a fixed coordinate

For a fixed translated endpoint v and active coordinate c, two WholeCubeQTPair
partners s1,s2 have

  Q_s1 = T_c(v) = Q_s2

and the same retained-active palette.

If s1,s2 are distinct projected-loss vertices, their mutual edge is retained.
At its retained colour e, the common completion cube forces the same retained
bit at s1 and s2, while edge orientation forces false at the lower endpoint
and true at the upper endpoint. Contradiction.

Thus, among projected-loss vertices, one active coordinate of v has at most one
whole-cube partner.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem projectedLoss_wholeCube_partner_unique_at_coordinate
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {v s₁ s₂ : V} {c : Fin n}
    (hs1Loss : s₁ ∈ projectedLossVertices C exponent)
    (hs2Loss : s₂ ∈ projectedLossVertices C exponent)
    (h₁ : WholeCubeQTPair C s₁ v c)
    (h₂ : WholeCubeQTPair C s₂ v c) :
    s₁ = s₂ := by
  by_contra hne
  have hQeq :
      retainedCompletionWords C s₁ =
        retainedCompletionWords C s₂ := by
    rcases h₁ with ⟨_,hEq1⟩
    rcases h₂ with ⟨_,hEq2⟩
    exact hEq1.symm.trans hEq2

  have hnonempty :
      (retainedCompletionWords C s₁).Nonempty := by
    rw [retainedCompletionWords_nonempty_iff]
  obtain ⟨word,hword1⟩ := hnonempty
  have hword2 :
      word ∈ retainedCompletionWords C s₂ := by
    rw [← hQeq]
    exact hword1

  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hret :
        (C.color s₁ s₂).val < n :=
      projectedLoss_edge_right_retained
        C exponent hexp honeLoss hs1Loss hlt
    let e : Fin n := retainedColor C s₁ s₂ hret
    have he1 :
        e ∈ retainedActive C s₁ :=
      retainedColor_mem_retainedActive_left C hlt hret
    have he2 :
        e ∈ retainedActive C s₂ :=
      retainedColor_mem_retainedActive_right C hlt hret
    have hbit1 :=
      (mem_retainedCompletionWords C s₁ word).1
        hword1 e he1
    have hbit2 :=
      (mem_retainedCompletionWords C s₂ word).1
        hword2 e he2
    have hOut1 : e ∈ outgoingRetained C s₁ := by
      apply (mem_outgoingRetained_iff C s₁ e).2
      refine ⟨s₂,hlt,?_⟩
      rfl
    have hIn2 : e ∈ incomingRetained C s₂ := by
      apply (mem_incomingRetained_iff C s₂ e).2
      refine ⟨s₁,hlt,?_⟩
      rfl
    have hb1 :
        retainedBit C s₁ e = false :=
      retainedBit_false_of_outgoingRetained C hOut1
    have hb2 :
        retainedBit C s₂ e = true :=
      (mem_incomingRetained_iff_retainedBit_true C s₂ e).1 hIn2
    rw [hbit1,hbit2] at hb1 hb2
    simp_all
  · have hret :
        (C.color s₂ s₁).val < n :=
      projectedLoss_edge_right_retained
        C exponent hexp honeLoss hs2Loss hgt
    let e : Fin n := retainedColor C s₂ s₁ hret
    have he2 :
        e ∈ retainedActive C s₂ :=
      retainedColor_mem_retainedActive_left C hgt hret
    have he1 :
        e ∈ retainedActive C s₁ :=
      retainedColor_mem_retainedActive_right C hgt hret
    have hbit1 :=
      (mem_retainedCompletionWords C s₁ word).1
        hword1 e he1
    have hbit2 :=
      (mem_retainedCompletionWords C s₂ word).1
        hword2 e he2
    have hOut2 : e ∈ outgoingRetained C s₂ := by
      apply (mem_outgoingRetained_iff C s₂ e).2
      refine ⟨s₁,hgt,?_⟩
      rfl
    have hIn1 : e ∈ incomingRetained C s₁ := by
      apply (mem_incomingRetained_iff C s₁ e).2
      refine ⟨s₂,hgt,?_⟩
      rfl
    have hb2 :
        retainedBit C s₂ e = false :=
      retainedBit_false_of_outgoingRetained C hOut2
    have hb1 :
        retainedBit C s₁ e = true :=
      (mem_incomingRetained_iff_retainedBit_true C s₁ e).1 hIn1
    rw [hbit1,hbit2] at hb1 hb2
    simp_all

#print axioms projectedLoss_wholeCube_partner_unique_at_coordinate

end OrderedEdgeColoring
end JSP000404Research
