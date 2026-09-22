import JSP000404Research.ResidualSameCodeOrientation
import Mathlib.Tactic

/-!
# Safe targets of hard residual pairs are new at the upper endpoint

ResidualSameCodeOrientation already proves that a locally safe target for a
same-retained pair cannot be absorbed at both endpoints.

The stronger one-sided statement is true.

For a same-retained pair u<v, a safe target c avoids

  incomingRetained(u) union outgoingRetained(v).

Equality of retained codes makes the incoming retained sets of u and v equal,
so c is not incoming at v either.  If c were retained-active at v, the
incoming/outgoing decomposition would force c to be outgoing at v, contradicting
safety.

Hence every safe recolouring target for a hard residual pair creates a new
retained-active colour at the upper endpoint.  In particular, a saturated
upper endpoint cannot be handled by ordinary safe residual recolouring without
some compensating mechanism.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Main rigidity theorem: for a same-retained pair, every locally safe
retained target is inactive at the upper endpoint. -/
theorem safe_target_not_retainedActive_upper_of_sameRetained
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hsame : SameRetained C u v)
    {c : Fin n}
    (hsafe : c ∉ residualForbidden C u v) :
    c ∉ retainedActive C v := by
  have hnotInU : c ∉ incomingRetained C u := by
    intro h
    exact hsafe (Finset.mem_union_left _ h)
  have hnotOutV : c ∉ outgoingRetained C v := by
    intro h
    exact hsafe (Finset.mem_union_right _ h)
  have hnotInV : c ∉ incomingRetained C v := by
    rw [← incomingRetained_eq_of_sameRetained C hsame]
    exact hnotInU
  rw [retainedActive_eq_incoming_union_outgoing C v]
  intro hactive
  rw [Finset.mem_union] at hactive
  rcases hactive with hInV | hOutV
  · exact hnotInV hInV
  · exact hnotOutV hOutV

/-- Ordered hard-residual specialization. -/
theorem safe_target_not_retainedActive_upper_of_hardResidual
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (_huv : u < v)
    (hhard : HardResidual C u v)
    {c : Fin n}
    (hsafe : c ∉ residualForbidden C u v) :
    c ∉ retainedActive C v := by
  have hsame :
      SameRetained C u v :=
    (not_retainedSeparated_iff C u v).1 hhard.2
  exact safe_target_not_retainedActive_upper_of_sameRetained
    C hsame hsafe

/-- Rephrased as an impossibility of zero-growth repair at a saturated upper
endpoint. -/
theorem no_safe_target_in_retainedActive_upper_of_sameRetained
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hsame : SameRetained C u v) :
    ¬ ∃ c : Fin n,
      c ∉ residualForbidden C u v ∧
      c ∈ retainedActive C v := by
  rintro ⟨c, hsafe, hactive⟩
  exact
    (safe_target_not_retainedActive_upper_of_sameRetained
      C hsame hsafe) hactive

#print axioms safe_target_not_retainedActive_upper_of_sameRetained
#print axioms safe_target_not_retainedActive_upper_of_hardResidual
#print axioms no_safe_target_in_retainedActive_upper_of_sameRetained

end OrderedEdgeColoring
end JSP000404Research
