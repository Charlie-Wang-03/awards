import JSP000404Research.ResidualCompletionAccounting
import Mathlib.Tactic

/-!
# Residual bit labels completion fibres injectively

The proof of the global fibre bound card <= 2 already uses the fact that two
distinct carriers of the same retained word must have opposite residual bits.

This file exposes the pointwise form as a reusable theorem.  It is the natural
label used to inject blocker incidences into source-word × Bool.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem completion_carriers_eq_of_residualBit_eq
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {word : Fin n → Bool}
    {u v : V}
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v)
    (hbit :
      bit C u (residualCoord n) =
        bit C v (residualCoord n)) :
    u = v := by
  by_contra huv
  rcases retainedCompletion_overlap_forces_residual
      C huv hu hv with hres | hres
  · have hcol :
        C.color u v = residualCoord n := by
      apply Fin.ext
      simpa [residualCoord] using residual_val_eq C hres.2
    have hne := edgeColor_bit_ne C hres.1
    rw [hcol] at hne
    exact hne hbit
  · have hcol :
        C.color v u = residualCoord n := by
      apply Fin.ext
      simpa [residualCoord] using residual_val_eq C hres.2
    have hne := edgeColor_bit_ne C hres.1
    rw [hcol] at hne
    exact hne hbit.symm

theorem completionFibre_residualBit_injective
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (word : Fin n → Bool) :
    Function.Injective
      (fun v : {x : V // x ∈ completionFibre C word} =>
        bit C v.1 (residualCoord n)) := by
  intro u v huv
  apply Subtype.ext
  apply completion_carriers_eq_of_residualBit_eq C
  · exact (mem_completionFibre C word u.1).1 u.2
  · exact (mem_completionFibre C word v.1).1 v.2
  · exact huv

#print axioms completion_carriers_eq_of_residualBit_eq
#print axioms completionFibre_residualBit_injective

end OrderedEdgeColoring
end JSP000404Research
