import JSP000404Research.ResidualSafeSupportOrientation
import JSP000404Research.ResidualPairFlipBlocker
import JSP000404Research.ResidualInactiveUniqueCode
import Mathlib.Tactic

/-!
# One-sided blocker geometry for common-active support displacement

Let u<v carry a common completion word, hence u--v is residual.  Flip a
coordinate c active at both endpoints.

If c is outgoing at both endpoints, every blocker of the flipped word lies
strictly to the right of u.  Indeed a blocker w<u gives two alternatives for
the edge w--u:

* retained: its colour must be c, forcing c incoming at u, contradicting
  outgoing orientation;
* residual: w--u--v is a forbidden monochromatic residual two-path.

Dually, if c is incoming at both endpoints, every blocker lies strictly to the
left of v.

This is the triangular support needed to order common-active pair
displacements globally.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem oneFlip_blocker_edge_retained_colour_or_residual
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u w : V} {word : Fin n → Bool} {c : Fin n}
    (huw : u ≠ w)
    (huWord : word ∈ retainedCompletionWords C u)
    (hcU : c ∈ retainedActive C u)
    (hwFlip :
      flipBoolWordAt word c ∈ retainedCompletionWords C w) :
    (
      ∃ huwlt : u < w,
        (IsResidual C u w ∨
          ∃ hret : (C.color u w).val < n,
            retainedColor C u w hret = c)
    )
    ∨
    (
      ∃ hwult : w < u,
        (IsResidual C w u ∨
          ∃ hret : (C.color w u).val < n,
            retainedColor C w u hret = c)
    ) := by
  rcases lt_or_gt_of_ne huw with huwlt | hwult
  · left
    refine ⟨huwlt,?_⟩
    by_cases hret : (C.color u w).val < n
    · right
      refine ⟨hret,?_⟩
      let e : Fin n := retainedColor C u w hret
      by_contra hec
      have heU :
          e ∈ retainedActive C u :=
        retainedColor_mem_retainedActive_left
          C huwlt hret
      have heW :
          e ∈ retainedActive C w :=
        retainedColor_mem_retainedActive_right
          C huwlt hret
      have huComp :=
        (mem_retainedCompletionWords C u word).1 huWord
      have hwComp :=
        (mem_retainedCompletionWords C w
          (flipBoolWordAt word c)).1 hwFlip
      have huAt := huComp e heU
      have hwAt := hwComp e heW
      have hec' : e ≠ c := by
        intro h
        exact hec (by simpa [e] using h)
      rw [flipBoolWordAt_off word hec'] at hwAt
      have hbits :
          retainedBit C u e = retainedBit C w e :=
        huAt.symm.trans hwAt
      exact
        (retainedBit_ne_of_retained_edge C huwlt hret) hbits
    · left
      exact hret
  · right
    refine ⟨hwult,?_⟩
    by_cases hret : (C.color w u).val < n
    · right
      refine ⟨hret,?_⟩
      let e : Fin n := retainedColor C w u hret
      by_contra hec
      have heW :
          e ∈ retainedActive C w :=
        retainedColor_mem_retainedActive_left
          C hwult hret
      have heU :
          e ∈ retainedActive C u :=
        retainedColor_mem_retainedActive_right
          C hwult hret
      have huComp :=
        (mem_retainedCompletionWords C u word).1 huWord
      have hwComp :=
        (mem_retainedCompletionWords C w
          (flipBoolWordAt word c)).1 hwFlip
      have huAt := huComp e heU
      have hwAt := hwComp e heW
      have hec' : e ≠ c := by
        intro h
        exact hec (by simpa [e] using h)
      rw [flipBoolWordAt_off word hec'] at hwAt
      have hbits :
          retainedBit C w e = retainedBit C u e :=
        hwAt.symm.trans huAt
      exact
        (retainedBit_ne_of_retained_edge C hwult hret) hbits
    · left
      exact hret

theorem commonOutgoing_oneFlip_blocker_right_of_lower
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {word : Fin n → Bool} {c : Fin n}
    (huv : u < v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hcU : c ∈ retainedActive C u)
    (hcV : c ∈ retainedActive C v)
    (hcOutU : c ∈ outgoingRetained C u)
    (hcOutV : c ∈ outgoingRetained C v)
    (hwFlip :
      flipBoolWordAt word c ∈ retainedCompletionWords C w) :
    u < w := by
  have hwu : w ≠ u := by
    intro h
    subst w
    exact (flip_active_not_mem_completion C huWord hcU) hwFlip
  have hresUV :=
    isResidual_of_retainedCompletion_overlap_lt
      C huv huWord hvWord
  rcases oneFlip_blocker_edge_retained_colour_or_residual
      C hwu.symm huWord hcU hwFlip with hright | hleft
  · exact hright.1
  · obtain ⟨hwult,hcase⟩ := hleft
    rcases hcase with hresWU | hret
    · exact False.elim
        (no_two_residual_on_path C hwult huv hresWU hresUV)
    · obtain ⟨hret,hcol⟩ := hret
      have hcInU : c ∈ incomingRetained C u := by
        apply (mem_incomingRetained_iff C u c).2
        refine ⟨w,hwult,?_⟩
        apply Fin.ext
        have hval := congrArg Fin.val hcol
        simpa [retainedColor] using hval
      exact False.elim
        (Finset.disjoint_left.mp
          (incomingRetained_disjoint_outgoingRetained C u)
          hcInU hcOutU)

theorem commonIncoming_oneFlip_blocker_left_of_upper
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {word : Fin n → Bool} {c : Fin n}
    (huv : u < v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hcU : c ∈ retainedActive C u)
    (hcV : c ∈ retainedActive C v)
    (hcInU : c ∈ incomingRetained C u)
    (hcInV : c ∈ incomingRetained C v)
    (hwFlip :
      flipBoolWordAt word c ∈ retainedCompletionWords C w) :
    w < v := by
  have hwv : w ≠ v := by
    intro h
    subst w
    exact (flip_active_not_mem_completion C hvWord hcV) hwFlip
  rcases lt_or_gt_of_ne hwv with hwvlt | hvwlt
  · exact hwvlt
  · have hresUV :=
      isResidual_of_retainedCompletion_overlap_lt
        C huv huWord hvWord
    rcases oneFlip_blocker_edge_retained_colour_or_residual
        C (ne_of_lt hvwlt) hvWord hcV hwFlip
      with hright | hleft
    · obtain ⟨hvw,hcase⟩ := hright
      rcases hcase with hresVW | hret
      · exact False.elim
          (no_two_residual_on_path C huv hvw hresUV hresVW)
      · obtain ⟨hret,hcol⟩ := hret
        have hcOutV : c ∈ outgoingRetained C v := by
          apply (mem_outgoingRetained_iff C v c).2
          refine ⟨w,hvw,?_⟩
          apply Fin.ext
          have hval := congrArg Fin.val hcol
          simpa [retainedColor] using hval
        exact False.elim
          (Finset.disjoint_left.mp
            (incomingRetained_disjoint_outgoingRetained C v)
            hcInV hcOutV)
    · exact False.elim
        ((not_lt_of_ge (le_of_lt hvwlt)) hleft.1)

#print axioms oneFlip_blocker_edge_retained_colour_or_residual
#print axioms commonOutgoing_oneFlip_blocker_right_of_lower
#print axioms commonIncoming_oneFlip_blocker_left_of_upper

end OrderedEdgeColoring
end JSP000404Research
