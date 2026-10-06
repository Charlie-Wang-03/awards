import JSP000404Research.ResidualWholeCubeTQTwoFlip
import JSP000404Research.WholeCubeQTPairCore
import JSP000404Research.RetainedOrientation
import Mathlib.Tactic

/-!
# Orientation profile of the whole-cube T/Q augmentation

For a WholeCubeQTPair (s,v,c), the retained codes of s and v agree at every
active coordinate d != c.  In a T/Q augmentation along such a d, the edge
v--w has retained colour d, so d is active at w.  The two-flip relation then
forces the w-bit at d to be the opposite of the common s/v bit.

Thus at coordinate d the three vertices have profile

  bit(s,d) = bit(v,d) != bit(w,d).

Moreover the direction of the d-coloured edge v--w determines the common
Boolean value explicitly:
* v<w  -> bit(v,d)=bit(s,d)=false, bit(w,d)=true;
* w<v  -> bit(v,d)=bit(s,d)=true,  bit(w,d)=false.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem wholeCube_TQ_three_vertex_bit_profile
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s v w : V} {c d : Fin n}
    (hcV : c ∈ retainedActive C v)
    (hdV : d ∈ retainedActive C v)
    (hdc : d ≠ c)
    (hwhole : WholeCubeQTPair C s v c)
    {word : Fin n → Bool}
    (hvT : word ∈ translatedCompletionWords C v d)
    (hwQ : word ∈ retainedCompletionWords C w)
    (hdW : d ∈ retainedActive C w) :
    retainedBit C s d = retainedBit C v d ∧
    retainedBit C w d = !(retainedBit C v d) := by
  have hsv :=
    wholeCube_off_owner_retainedBit_eq
      C hwhole hdV hdc
  have hws :=
    wholeCube_TQ_bit_opposite_at_d_of_active
      C hcV hdV hdc hwhole hvT hwQ hdW
  refine ⟨hsv,?_⟩
  rw [← hsv]
  exact hws

theorem wholeCube_TQ_ordered_orientation_profile
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s v w : V} {c d : Fin n}
    (hcV : c ∈ retainedActive C v)
    (hdV : d ∈ retainedActive C v)
    (hdc : d ≠ c)
    (hwhole : WholeCubeQTPair C s v c)
    {word : Fin n → Bool}
    (hvT : word ∈ translatedCompletionWords C v d)
    (hwQ : word ∈ retainedCompletionWords C w)
    (hedge :
      (∃ hvw : v < w,
        ∃ hret : (C.color v w).val < n,
          retainedColor C v w hret = d)
      ∨
      (∃ hwv : w < v,
        ∃ hret : (C.color w v).val < n,
          retainedColor C w v hret = d)) :
    (
      v < w ∧
      retainedBit C s d = false ∧
      retainedBit C v d = false ∧
      retainedBit C w d = true
    )
    ∨
    (
      w < v ∧
      retainedBit C s d = true ∧
      retainedBit C v d = true ∧
      retainedBit C w d = false
    ) := by
  rcases hedge with hedge | hedge
  · obtain ⟨hvw,hret,hcol⟩ := hedge
    have hdW :
        d ∈ retainedActive C w := by
      have hmem :=
        retainedColor_mem_retainedActive_right C hvw hret
      simpa [hcol] using hmem
    have hprof :=
      wholeCube_TQ_three_vertex_bit_profile
        C hcV hdV hdc hwhole hvT hwQ hdW
    have hdOutV :
        d ∈ outgoingRetained C v := by
      apply (mem_outgoingRetained_iff C v d).2
      refine ⟨w,hvw,?_⟩
      apply Fin.ext
      have hv := congrArg Fin.val hcol
      simpa [retainedColor] using hv
    have hdInW :
        d ∈ incomingRetained C w := by
      apply (mem_incomingRetained_iff C w d).2
      refine ⟨v,hvw,?_⟩
      apply Fin.ext
      have hv := congrArg Fin.val hcol
      simpa [retainedColor] using hv
    have hvFalse :=
      retainedBit_false_of_outgoingRetained C hdOutV
    have hwTrue :=
      (mem_incomingRetained_iff_retainedBit_true C w d).1 hdInW
    left
    exact ⟨hvw,
      hprof.1.trans hvFalse,
      hvFalse,
      hwTrue⟩
  · obtain ⟨hwv,hret,hcol⟩ := hedge
    have hdW :
        d ∈ retainedActive C w := by
      have hmem :=
        retainedColor_mem_retainedActive_left C hwv hret
      simpa [hcol] using hmem
    have hprof :=
      wholeCube_TQ_three_vertex_bit_profile
        C hcV hdV hdc hwhole hvT hwQ hdW
    have hdInV :
        d ∈ incomingRetained C v := by
      apply (mem_incomingRetained_iff C v d).2
      refine ⟨w,hwv,?_⟩
      apply Fin.ext
      have hv := congrArg Fin.val hcol
      simpa [retainedColor] using hv
    have hdOutW :
        d ∈ outgoingRetained C w := by
      apply (mem_outgoingRetained_iff C w d).2
      refine ⟨v,hwv,?_⟩
      apply Fin.ext
      have hv := congrArg Fin.val hcol
      simpa [retainedColor] using hv
    have hvTrue :=
      (mem_incomingRetained_iff_retainedBit_true C v d).1 hdInV
    have hwFalse :=
      retainedBit_false_of_outgoingRetained C hdOutW
    right
    exact ⟨hwv,
      hprof.1.trans hvTrue,
      hvTrue,
      hwFalse⟩

#print axioms wholeCube_TQ_three_vertex_bit_profile
#print axioms wholeCube_TQ_ordered_orientation_profile

end OrderedEdgeColoring
end JSP000404Research
