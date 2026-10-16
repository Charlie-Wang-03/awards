import JSP000404Research.CanonicalSignOrder
import JSP000404Research.CanonicalRayReversal
import Mathlib.Tactic

/-!
# Boolean ray sign and the reversed canonical point order

This equivalence is shared by middle-hidden sign-to-rank and
canonical-rank-band proofs. It belongs in a common upstream module,
not in either downstream consumer (which caused a missing declaration).
-/

namespace JSP000404Research

theorem raySign_false_iff_reverse_canonicalPointLt
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {i j : V}
    (hij : i ≠ j) :
    raySignAt hp i (⟨j, hij.symm⟩ : OtherVertex i) = false
      ↔
    CanonicalPointLt p j i := by
  rw [← raySign_true_iff_canonicalPointLt hp hij.symm]
  rw [raySignAt_reverse_eq_not hp hij]
  cases h :
      raySignAt hp i (⟨j, hij.symm⟩ : OtherVertex i) <;>
    simp

#print axioms raySign_false_iff_reverse_canonicalPointLt

end JSP000404Research
