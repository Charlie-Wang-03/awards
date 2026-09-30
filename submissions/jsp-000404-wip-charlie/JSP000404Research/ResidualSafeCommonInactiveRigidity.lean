import JSP000404Research.ResidualSafeSaturatedTransition
import JSP000404Research.ResidualUnsafeOverlapOrientation
import Mathlib.Tactic

/-!
# Support-unsafe rigidity of the final safe common-inactive subtype

A safe overlap is genuinely non-deterministic only when every safe coordinate
is inactive at both endpoints.  If some safe coordinate is active at one
endpoint, the existing anchored deterministic transition applies.

Under this no-active-safe hypothesis, the safe coordinates are exactly the
common-inactive coordinates.  Equivalently,

  residualForbidden(u,v)
    = retainedActive(u) union retainedActive(v).

Thus after deleting the common-inactive free tensor factor, the remaining
active support is completely unsafe.

The same orientation nesting as for a genuinely unsafe overlap follows on
this active support:

  outgoing(u) subset outgoing(v),
  incoming(v) subset incoming(u).
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

def NoActiveSafeCoordinate
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) : Prop :=
  ∀ c : Fin n,
    c ∉ residualForbidden C u v →
    c ∉ retainedActive C u ∧
      c ∉ retainedActive C v

theorem safe_iff_commonInactive_of_noActiveSafe
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hno : NoActiveSafeCoordinate C u v)
    (c : Fin n) :
    c ∉ residualForbidden C u v ↔
      c ∈ commonInactiveRetained C u v := by
  constructor
  · intro hsafe
    exact (mem_commonInactiveRetained C u v c).2
      (hno c hsafe)
  · intro hcommon
    have hdata :=
      (mem_commonInactiveRetained C u v c).1 hcommon
    unfold residualForbidden
    rw [Finset.mem_union]
    push_neg
    constructor
    · intro hIn
      exact hdata.1
        (incomingRetained_subset_retainedActive C u hIn)
    · intro hOut
      exact hdata.2
        (outgoingRetained_subset_retainedActive C v hOut)

theorem residualForbidden_eq_active_union_of_noActiveSafe
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hno : NoActiveSafeCoordinate C u v) :
    residualForbidden C u v =
      retainedActive C u ∪ retainedActive C v := by
  classical
  ext c
  constructor
  · intro hforbid
    unfold residualForbidden at hforbid
    rw [Finset.mem_union] at hforbid
    rw [Finset.mem_union]
    rcases hforbid with hIn | hOut
    · exact Or.inl
        (incomingRetained_subset_retainedActive C u hIn)
    · exact Or.inr
        (outgoingRetained_subset_retainedActive C v hOut)
  · intro hactive
    by_contra hnotForbid
    have hinactive := hno c hnotForbid
    rw [Finset.mem_union] at hactive
    rcases hactive with hu | hv
    · exact hinactive.1 hu
    · exact hinactive.2 hv

theorem active_union_disjoint_commonInactive_of_noActiveSafe
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hno : NoActiveSafeCoordinate C u v) :
    Disjoint
      (residualForbidden C u v)
      (commonInactiveRetained C u v) := by
  classical
  rw [Finset.disjoint_left]
  intro c hforbid hcommon
  exact
    (safe_iff_commonInactive_of_noActiveSafe C hno c).2
      hcommon hforbid

theorem forbidden_union_commonInactive_eq_univ_of_noActiveSafe
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hno : NoActiveSafeCoordinate C u v) :
    residualForbidden C u v ∪
      commonInactiveRetained C u v =
        (Finset.univ : Finset (Fin n)) := by
  classical
  ext c
  simp only [Finset.mem_union, Finset.mem_univ, iff_true]
  by_cases hforbid : c ∈ residualForbidden C u v
  · exact Or.inl hforbid
  · exact Or.inr
      ((safe_iff_commonInactive_of_noActiveSafe
        C hno c).1 hforbid)

theorem outgoing_subset_right_of_noActiveSafe_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hno : NoActiveSafeCoordinate C u v) :
    outgoingRetained C u ⊆ outgoingRetained C v := by
  intro c hcOutU
  have hcActiveU :
      c ∈ retainedActive C u :=
    outgoingRetained_subset_retainedActive C u hcOutU
  have hcUnion :
      c ∈ retainedActive C u ∪ retainedActive C v :=
    Finset.mem_union_left _ hcActiveU
  have hcForbid :
      c ∈ residualForbidden C u v := by
    rw [residualForbidden_eq_active_union_of_noActiveSafe
      C hno]
    exact hcUnion
  unfold residualForbidden at hcForbid
  rw [Finset.mem_union] at hcForbid
  rcases hcForbid with hcInU | hcOutV
  · exact False.elim
      (Finset.disjoint_left.mp
        (incomingRetained_disjoint_outgoingRetained C u)
        hcInU hcOutU)
  · exact hcOutV

theorem incoming_subset_left_of_noActiveSafe_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hno : NoActiveSafeCoordinate C u v) :
    incomingRetained C v ⊆ incomingRetained C u := by
  intro c hcInV
  have hcActiveV :
      c ∈ retainedActive C v :=
    incomingRetained_subset_retainedActive C v hcInV
  have hcUnion :
      c ∈ retainedActive C u ∪ retainedActive C v :=
    Finset.mem_union_right _ hcActiveV
  have hcForbid :
      c ∈ residualForbidden C u v := by
    rw [residualForbidden_eq_active_union_of_noActiveSafe
      C hno]
    exact hcUnion
  unfold residualForbidden at hcForbid
  rw [Finset.mem_union] at hcForbid
  rcases hcForbid with hcInU | hcOutV
  · exact hcInU
  · exact False.elim
      (Finset.disjoint_left.mp
        (incomingRetained_disjoint_outgoingRetained C v)
        hcInV hcOutV)

#print axioms safe_iff_commonInactive_of_noActiveSafe
#print axioms residualForbidden_eq_active_union_of_noActiveSafe
#print axioms outgoing_subset_right_of_noActiveSafe_overlap
#print axioms incoming_subset_left_of_noActiveSafe_overlap

end OrderedEdgeColoring
end JSP000404Research
