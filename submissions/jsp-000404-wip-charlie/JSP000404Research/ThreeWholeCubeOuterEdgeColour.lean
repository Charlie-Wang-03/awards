import JSP000404Research.ThreeWholeCubeRetainedCodeStar
import JSP000404Research.RetainedOrientation
import Mathlib.Tactic

/-!
# Outer-edge colour restriction in a three-whole-cube code star

A retained edge u<v is outgoing at u and incoming at v, so its retained colour
has retained bit false at u and true at v.

Two whole-cube partners si,sj of a common source v differ from the source code
only at ci and cj respectively.  Hence their codes agree at every active
coordinate d distinct from ci,cj.  Their joining retained edge therefore
cannot have any such colour d.

Thus every outer edge si-sj is coloured by one of its two endpoint owner
coordinates ci,cj.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem retained_edge_colour_bits_false_true
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u w : V}
    (huw : u < w)
    (hret : (C.color u w).val < n) :
    let e := retainedColor C u w hret
    retainedBit C u e = false ∧
    retainedBit C w e = true := by
  let e := retainedColor C u w hret
  have hOut :
      e ∈ outgoingRetained C u :=
    retainedColor_mem_outgoingRetained_left C huw hret
  have hIn :
      e ∈ incomingRetained C w :=
    retainedColor_mem_incomingRetained_right C huw hret
  exact ⟨
    retainedBit_false_of_outgoingRetained C hOut,
    (mem_incomingRetained_iff_retainedBit_true C w e).1 hIn
  ⟩

theorem wholeCube_partner_pair_edge_colour_two_owner
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v s₁ s₂ : V}
    {c₁ c₂ : Fin n}
    (hc12 : c₁ ≠ c₂)
    (hc1V : c₁ ∈ retainedActive C v)
    (hc2V : c₂ ∈ retainedActive C v)
    (h₁ : WholeCubeQTPair C s₁ v c₁)
    (h₂ : WholeCubeQTPair C s₂ v c₂)
    (hs12 :
      (∃ hlt : s₁ < s₂,
        ∃ hret : (C.color s₁ s₂).val < n,
          True)
      ∨
      (∃ hlt : s₂ < s₁,
        ∃ hret : (C.color s₂ s₁).val < n,
          True)) :
    (
      ∃ hlt : s₁ < s₂,
      ∃ hret : (C.color s₁ s₂).val < n,
        retainedColor C s₁ s₂ hret = c₁ ∨
        retainedColor C s₁ s₂ hret = c₂
    )
    ∨
    (
      ∃ hlt : s₂ < s₁,
      ∃ hret : (C.color s₂ s₁).val < n,
        retainedColor C s₂ s₁ hret = c₁ ∨
        retainedColor C s₂ s₁ hret = c₂
    ) := by
  have hcode1 :=
    wholeCube_retainedCode_single_flip C hc1V h₁
  have hcode2 :=
    wholeCube_retainedCode_single_flip C hc2V h₂
  rcases hs12 with h12 | h21
  · obtain ⟨hlt,hret,_⟩ := h12
    let e := retainedColor C s₁ s₂ hret
    have hbits :=
      retained_edge_colour_bits_false_true C hlt hret
    have heActive1 :
        e ∈ retainedActive C s₁ :=
      retainedColor_mem_retainedActive_left C hlt hret
    have heV :
        e ∈ retainedActive C v := by
      rw [← hcode1.1]
      exact heActive1
    by_cases he1 : e = c₁
    · left
      exact ⟨hlt,hret,Or.inl he1⟩
    by_cases he2 : e = c₂
    · left
      exact ⟨hlt,hret,Or.inr he2⟩
    have hb1 :
        retainedBit C s₁ e = retainedBit C v e :=
      hcode1.2.2 e heV he1
    have hb2 :
        retainedBit C s₂ e = retainedBit C v e :=
      hcode2.2.2 e heV he2
    rw [hb1,hb2] at hbits
    simp_all
  · obtain ⟨hlt,hret,_⟩ := h21
    let e := retainedColor C s₂ s₁ hret
    have hbits :=
      retained_edge_colour_bits_false_true C hlt hret
    have heActive2 :
        e ∈ retainedActive C s₂ :=
      retainedColor_mem_retainedActive_left C hlt hret
    have heV :
        e ∈ retainedActive C v := by
      rw [← hcode2.1]
      exact heActive2
    by_cases he1 : e = c₁
    · right
      exact ⟨hlt,hret,Or.inl he1⟩
    by_cases he2 : e = c₂
    · right
      exact ⟨hlt,hret,Or.inr he2⟩
    have hb2 :
        retainedBit C s₂ e = retainedBit C v e :=
      hcode2.2.2 e heV he2
    have hb1 :
        retainedBit C s₁ e = retainedBit C v e :=
      hcode1.2.2 e heV he1
    rw [hb2,hb1] at hbits
    simp_all

#print axioms retained_edge_colour_bits_false_true
#print axioms wholeCube_partner_pair_edge_colour_two_owner

end OrderedEdgeColoring
end JSP000404Research
