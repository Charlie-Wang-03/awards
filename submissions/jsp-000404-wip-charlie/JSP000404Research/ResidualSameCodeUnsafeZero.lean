
import JSP000404Research.ResidualSameCodeExactOrientation
import Mathlib.Tactic

/-!
# Unsafe same-retained pairs are exactly zero-free upper endpoints

For an ordered pair u,v with the same retained canonical code,
ResidualSameCodeExactOrientation proves the exact set identity

  safeTargetSet(u,v) = retainedInactive(v).

Therefore the pair has no safe retained target iff the upper endpoint has no
retained free coordinate.

Equivalently,

  unsafe(u,v) <-> projectedFree(v)=0.

If the upper endpoint is exact in the projected profile, this is further
equivalent to target exponent(v)=0.

So every saturated same-code pair whose upper endpoint has positive exponent
automatically admits a safe retained target.  The genuinely unsafe saturated
same-code branch is forced to carry a zero-exponent upper endpoint.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem no_safeTarget_iff_retainedInactive_upper_empty_of_sameRetained
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hsame : SameRetained C u v) :
    (¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
      ↔
    retainedInactive C v = ∅ := by
  classical
  have hset :=
    safeTargetSet_eq_retainedInactive_upper_of_sameRetained
      C hsame
  constructor
  · intro hunsafe
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro c hc
    have hcSafeSet :
        c ∈ Finset.univ  residualForbidden C u v := by
      rw [hset]
      exact hc
    have hcSafe :
        c ∉ residualForbidden C u v := by
      simpa using hcSafeSet
    exact hunsafe ⟨c, hcSafe⟩
  · intro hempty
    rintro ⟨c, hcSafe⟩
    have hcSet :
        c ∈ Finset.univ  residualForbidden C u v := by
      simp [hcSafe]
    rw [hset, hempty] at hcSet
    simp at hcSet

theorem no_safeTarget_iff_projectedFree_upper_zero_of_sameRetained
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hsame : SameRetained C u v) :
    (¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
      ↔
    projectedFree C v = 0 := by
  rw [no_safeTarget_iff_retainedInactive_upper_empty_of_sameRetained
      C hsame]
  unfold projectedFree
  rw [← retainedInactive_card C v]
  exact Finset.card_eq_zero

theorem exists_safeTarget_of_sameRetained_projectedFree_pos
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hsame : SameRetained C u v)
    (hpos : 0 < projectedFree C v) :
    ∃ c : Fin n, c ∉ residualForbidden C u v := by
  by_contra hno
  have hzero :=
    (no_safeTarget_iff_projectedFree_upper_zero_of_sameRetained
      C hsame).1 hno
  omega

theorem no_safeTarget_iff_exponent_upper_zero_of_sameRetained_exact
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V}
    (hsame : SameRetained C u v)
    (hvExact : ExactProjectedBudget C exponent v) :
    (¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
      ↔
    exponent v = 0 := by
  rw [no_safeTarget_iff_projectedFree_upper_zero_of_sameRetained
      C hsame]
  rw [hvExact]

theorem exists_safeTarget_of_sameRetained_exact_positive
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V}
    (hsame : SameRetained C u v)
    (hvExact : ExactProjectedBudget C exponent v)
    (hvPos : 1 ≤ exponent v) :
    ∃ c : Fin n, c ∉ residualForbidden C u v := by
  by_contra hno
  have hzero :=
    (no_safeTarget_iff_exponent_upper_zero_of_sameRetained_exact
      C exponent hsame hvExact).1 hno
  omega

/-- In the no-common-inactive hard branch, every safe target is exactly an
outgoing-only colour of the lower endpoint. -/
theorem safeTargetSet_eq_outgoingLower_sdiff_outgoingUpper
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hsame : SameRetained C u v)
    (hnoCommon :
      ¬ ∃ c : Fin n,
        c ∉ retainedActive C u ∧
        c ∉ retainedActive C v) :
    (Finset.univ  residualForbidden C u v) =
      outgoingRetained C u  outgoingRetained C v := by
  rw [safeTargetSet_eq_retainedInactive_upper_of_sameRetained
      C hsame,
      retainedInactive_right_eq_outgoingLeft_sdiff_outgoingRight
        C hsame hnoCommon]

#print axioms no_safeTarget_iff_projectedFree_upper_zero_of_sameRetained
#print axioms exists_safeTarget_of_sameRetained_projectedFree_pos
#print axioms no_safeTarget_iff_exponent_upper_zero_of_sameRetained_exact
#print axioms exists_safeTarget_of_sameRetained_exact_positive
#print axioms safeTargetSet_eq_outgoingLower_sdiff_outgoingUpper

end OrderedEdgeColoring
end JSP000404Research
