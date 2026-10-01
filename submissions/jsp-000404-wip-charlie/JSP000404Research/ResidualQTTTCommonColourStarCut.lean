import JSP000404Research.ResidualQTTTCommonColourBitCut
import JSP000404Research.ResidualLossTranslatedConflict
import JSP000404Research.ResidualSameCodeOrientation
import Mathlib.Tactic

/-!
# Internal star cut of a common Q/T/T/T retained colour

A retained edge colour forces opposite retained bits at its two endpoints.
Combined with the 3-vs-1 common-colour bit pattern of a saturated Q/T/T/T
word, this means that, if the common colour is cx, no edge among s,y,z can
have retained colour cx.  The analogous statements hold for cy and cz.

Thus inside the four Q/T/T/T vertices the common colour can occur only on
edges incident to its unique translated owner.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem retained_edge_colour_forces_opposite_bits
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (huv : u < v)
    (hret : (C.color u v).val < n)
    {d : Fin n}
    (hcol : retainedColor C u v hret = d) :
    retainedBit C u d ≠ retainedBit C v d := by
  have hOut : d ∈ outgoingRetained C u := by
    apply (mem_outgoingRetained_iff C u d).2
    refine ⟨v,huv,?_⟩
    exact hcol
  have hIn : d ∈ incomingRetained C v := by
    apply (mem_incomingRetained_iff C v d).2
    refine ⟨u,huv,?_⟩
    exact hcol
  have hfalse := retainedBit_false_of_outgoingRetained C hOut
  have htrue :=
    (mem_incomingRetained_iff_retainedBit_true C v d).1 hIn
  rw [hfalse,htrue]
  decide

theorem same_retained_bit_excludes_edge_colour
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (huv : u ≠ v)
    {d : Fin n}
    (hbits : retainedBit C u d = retainedBit C v d) :
    ∀ (hret :
      (C.color (min u v) (max u v)).val < n),
      retainedColor C (min u v) (max u v) hret ≠ d := by
  intro hret hcol
  rcases lt_or_gt_of_ne huv with huvlt | hvult
  · have hmin : min u v = u := min_eq_left huvlt.le
    have hmax : max u v = v := max_eq_right huvlt.le
    rw [hmin,hmax] at hret hcol
    exact
      (retained_edge_colour_forces_opposite_bits
        C huvlt hret hcol) hbits
  · have hmin : min u v = v := min_eq_right hvult.le
    have hmax : max u v = u := max_eq_left hvult.le
    rw [hmin,hmax] at hret hcol
    exact
      (retained_edge_colour_forces_opposite_bits
        C hvult hret hcol) hbits.symm

/-- If d=cx in the Q/T/T/T common-colour bit cut, then all three vertices
s,y,z share the same d-bit. -/
theorem QTTT_common_cx_same_bit_triple
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s x y z : V}
    {word : Fin n → Bool}
    {cx cy cz d : Fin n}
    (hcxy : cx ≠ cy)
    (hcxz : cx ≠ cz)
    (hcyz : cy ≠ cz)
    (hsd : d ∈ retainedActive C s)
    (hxd : d ∈ retainedActive C x)
    (hyd : d ∈ retainedActive C y)
    (hzd : d ∈ retainedActive C z)
    (hcxX : cx ∈ retainedActive C x)
    (hcyY : cy ∈ retainedActive C y)
    (hczZ : cz ∈ retainedActive C z)
    (hsQ : word ∈ retainedCompletionWords C s)
    (hxT : word ∈ translatedCompletionWords C x cx)
    (hyT : word ∈ translatedCompletionWords C y cy)
    (hzT : word ∈ translatedCompletionWords C z cz)
    (hd : d = cx) :
    retainedBit C s d = retainedBit C y d ∧
    retainedBit C s d = retainedBit C z d ∧
    retainedBit C y d = retainedBit C z d := by
  have hcut :=
    QTTT_common_colour_eq_cx_bit_cut
      C hcxy hcxz hcyz
      hsd hxd hyd hzd
      hcxX hcyY hczZ
      hsQ hxT hyT hzT hd
  exact ⟨hcut.2.1.symm,hcut.2.2.symm,
    hcut.2.1.trans hcut.2.2.symm⟩

#print axioms retained_edge_colour_forces_opposite_bits
#print axioms QTTT_common_cx_same_bit_triple

end OrderedEdgeColoring
end JSP000404Research
