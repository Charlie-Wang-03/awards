import JSP000404Research.ResidualSafeCommonInactiveRigidity
import Mathlib.Tactic

/-!
# Disjoint-active support-unsafe pairs have forced endpoint orientation

Suppose u<v is a no-active-safe overlap carrier and the retained-active sets of
u and v are disjoint.

Then every active retained coordinate at u must be incoming at u.  Indeed it is
inactive at v; if it were not incoming at u, it would lie outside
residualForbidden(u,v), hence would be a safe active coordinate.

Dually every active retained coordinate at v must be outgoing at v.

Therefore

  retainedActive(u) = incomingRetained(u),
  retainedActive(v) = outgoingRetained(v).

This is the exact orientation of the two-bit branch of the explicit pair-local
injection.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem active_left_subset_incoming_of_noActiveSafe_disjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hno : NoActiveSafeCoordinate C u v)
    (hdisj :
      Disjoint (retainedActive C u) (retainedActive C v)) :
    retainedActive C u ⊆ incomingRetained C u := by
  intro c hcU
  have hcNotV : c ∉ retainedActive C v := by
    intro hcV
    exact Finset.disjoint_left.mp hdisj hcU hcV
  by_contra hcNotIn
  have hcNotForbid :
      c ∉ residualForbidden C u v := by
    unfold residualForbidden
    rw [Finset.mem_union]
    push_neg
    constructor
    · exact hcNotIn
    · intro hcOutV
      exact hcNotV
        (outgoingRetained_subset_retainedActive C v hcOutV)
  exact (hno c hcNotForbid).1 hcU

theorem active_right_subset_outgoing_of_noActiveSafe_disjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hno : NoActiveSafeCoordinate C u v)
    (hdisj :
      Disjoint (retainedActive C u) (retainedActive C v)) :
    retainedActive C v ⊆ outgoingRetained C v := by
  intro c hcV
  have hcNotU : c ∉ retainedActive C u := by
    intro hcU
    exact Finset.disjoint_left.mp hdisj hcU hcV
  by_contra hcNotOut
  have hcNotForbid :
      c ∉ residualForbidden C u v := by
    unfold residualForbidden
    rw [Finset.mem_union]
    push_neg
    constructor
    · intro hcInU
      exact hcNotU
        (incomingRetained_subset_retainedActive C u hcInU)
    · exact hcNotOut
  exact (hno c hcNotForbid).2 hcV

theorem retainedActive_left_eq_incoming_of_noActiveSafe_disjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hno : NoActiveSafeCoordinate C u v)
    (hdisj :
      Disjoint (retainedActive C u) (retainedActive C v)) :
    retainedActive C u = incomingRetained C u := by
  apply Finset.Subset.antisymm
  · exact active_left_subset_incoming_of_noActiveSafe_disjoint
      C hno hdisj
  · exact incomingRetained_subset_retainedActive C u

theorem retainedActive_right_eq_outgoing_of_noActiveSafe_disjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hno : NoActiveSafeCoordinate C u v)
    (hdisj :
      Disjoint (retainedActive C u) (retainedActive C v)) :
    retainedActive C v = outgoingRetained C v := by
  apply Finset.Subset.antisymm
  · exact active_right_subset_outgoing_of_noActiveSafe_disjoint
      C hno hdisj
  · exact outgoingRetained_subset_retainedActive C v

#print axioms active_left_subset_incoming_of_noActiveSafe_disjoint
#print axioms active_right_subset_outgoing_of_noActiveSafe_disjoint
#print axioms retainedActive_left_eq_incoming_of_noActiveSafe_disjoint
#print axioms retainedActive_right_eq_outgoing_of_noActiveSafe_disjoint

end OrderedEdgeColoring
end JSP000404Research
