import JSP000404Research.ResidualHoleInjection
import Mathlib.Tactic

/-!
# Removing an active residual colour removes the one-unit palette loss

For an OrderedEdgeColoring by k+1 colours, the retained palette is obtained by
dropping the last colour.  If the total active palette at v has size at most
ell+1 and the residual colour is actually active at v, then the retained
palette has size at most ell.

This is the exact bridge between the one-exception phase estimate

  active(v) <= ell(v)+1

and residual-colour elimination.  Geometry no longer needs a globally good
phase.  It is enough to show that every vertex realizing the one-unit loss is
incident to the residual band.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem retainedActive_card_add_one_le_active_of_residual_mem
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1))
    (v : V)
    (hres : residualCoord k ∈ active C v) :
    (retainedActive C v).card + 1 ≤ (active C v).card := by
  classical
  let R : Finset (Fin (k + 1)) :=
    (retainedActive C v).map Fin.castSuccEmb
  have hRsub : R ⊆ active C v := by
    intro c hc
    rcases Finset.mem_map.mp hc with ⟨d, hd, rfl⟩
    exact (castSucc_mem_active_iff_mem_retainedActive C v d).2 hd
  have hresNotR : residualCoord k ∉ R := by
    intro h
    rcases Finset.mem_map.mp h with ⟨d, _hd, heq⟩
    have hval := congrArg Fin.val heq
    simp [residualCoord] at hval
  let S : Finset (Fin (k + 1)) := insert (residualCoord k) R
  have hSsub : S ⊆ active C v := by
    intro c hc
    rw [Finset.mem_insert] at hc
    rcases hc with rfl | hc
    · exact hres
    · exact hRsub hc
  have hcardS :
      S.card = (retainedActive C v).card + 1 := by
    dsimp [S]
    rw [Finset.card_insert_of_not_mem hresNotR]
    simp [R]
    omega
  have hcard := Finset.card_le_card hSsub
  rw [hcardS] at hcard
  exact hcard

theorem retainedActive_card_le_of_active_le_add_one_of_residual_mem
    {V : Type*} [LinearOrder V] {k ell : ℕ}
    (C : OrderedEdgeColoring V (k + 1))
    (v : V)
    (hactive : (active C v).card ≤ ell + 1)
    (hres : residualCoord k ∈ active C v) :
    (retainedActive C v).card ≤ ell := by
  have hdrop :=
    retainedActive_card_add_one_le_active_of_residual_mem C v hres
  omega

/-- Pointwise form: a one-loss active bound upgrades to an exact retained
bound whenever every truly over-budget vertex uses the residual colour. -/
theorem retainedActive_card_le_of_one_loss_and_bad_implies_residual
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1))
    (ell : V → ℕ)
    (honeLoss : ∀ v, (active C v).card ≤ ell v + 1)
    (hbadResidual :
      ∀ v, ell v < (active C v).card →
        residualCoord k ∈ active C v) :
    ∀ v, (retainedActive C v).card ≤ ell v := by
  intro v
  by_cases hgood : (active C v).card ≤ ell v
  · have hsub :
        (retainedActive C v).card ≤ (active C v).card := by
      classical
      let R : Finset (Fin (k + 1)) :=
        (retainedActive C v).map Fin.castSuccEmb
      have hRsub : R ⊆ active C v := by
        intro c hc
        rcases Finset.mem_map.mp hc with ⟨d, hd, rfl⟩
        exact (castSucc_mem_active_iff_mem_retainedActive C v d).2 hd
      have hc := Finset.card_le_card hRsub
      simpa [R] using hc
    exact hsub.trans hgood
  · have hbad : ell v < (active C v).card := by omega
    exact retainedActive_card_le_of_active_le_add_one_of_residual_mem
      C v (honeLoss v) (hbadResidual v hbad)

#print axioms retainedActive_card_add_one_le_active_of_residual_mem
#print axioms retainedActive_card_le_of_active_le_add_one_of_residual_mem
#print axioms retainedActive_card_le_of_one_loss_and_bad_implies_residual

end OrderedEdgeColoring
end JSP000404Research
