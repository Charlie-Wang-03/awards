
import JSP000404Research.ResidualOverlapDichotomy
import JSP000404Research.ResidualSameCodeOrientation
import Mathlib.Tactic

/-!
# Safe colours on hard residual pairs: the correct asymmetric form

For an ordered hard residual pair u<v with the same canonical retained code,
a locally safe retained colour c avoids

  incomingRetained(u) union outgoingRetained(v).

This condition is asymmetric in the two endpoints.

* If c is inactive at the lower endpoint u, then its retained bit is false at
  u and therefore also false at v.  If c were active at v, false bit would
  force c to be outgoing at v, contradicting safety.  Hence c is inactive at
  both endpoints.

* If c is inactive at the upper endpoint v, the same conclusion need not hold:
  c may be outgoing-active at u.  The exact dichotomy is therefore

    upper inactive => lower inactive OR lower outgoing-active.

So a safe hard overlap carrier either immediately exposes a common inactive
coordinate (when the safe coordinate is lower-inactive), or falls into one
specific oriented exceptional branch.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Safe plus lower-endpoint inactivity forces common inactivity. -/
theorem safe_colour_common_inactive_of_sameRetained_lower
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hsame : SameRetained C u v)
    {c : Fin n}
    (hsafe : c ∉ residualForbidden C u v)
    (hcu : c ∉ retainedActive C u) :
    c ∉ retainedActive C v := by
  intro hcv
  have huFalse :
      retainedBit C u c = false :=
    retainedBit_false_of_retained_inactive C hcu
  have hvFalse :
      retainedBit C v c = false := by
    rw [← hsame c]
    exact huFalse
  rw [retainedActive_eq_incoming_union_outgoing C v] at hcv
  rcases Finset.mem_union.mp hcv with hIn | hOut
  · have hvTrue :
        retainedBit C v c = true :=
      (mem_incomingRetained_iff_retainedBit_true
        C v c).1 hIn
    rw [hvFalse] at hvTrue
    contradiction
  · exact hsafe (Finset.mem_union_right _ hOut)

/-- If a safe colour is inactive at the upper endpoint, then at the lower
endpoint it is either inactive or outgoing-active. -/
theorem safe_upper_inactive_lower_inactive_or_outgoing
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    {c : Fin n}
    (hsafe : c ∉ residualForbidden C u v)
    (hcv : c ∉ retainedActive C v) :
    c ∉ retainedActive C u ∨
      c ∈ outgoingRetained C u := by
  by_cases hcu : c ∈ retainedActive C u
  · right
    rw [retainedActive_eq_incoming_union_outgoing C u] at hcu
    rcases Finset.mem_union.mp hcu with hIn | hOut
    · exact False.elim
        (hsafe (Finset.mem_union_left _ hIn))
    · exact hOut
  · exact Or.inl hcu

/-- Exact safe-hard-overlap alternative obtained from the general overlap
dichotomy. -/
theorem safe_sameRetained_overlap_commonInactive_or_oriented
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (hsame : SameRetained C u v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hsafe :
      ∃ c : Fin n, c ∉ residualForbidden C u v) :
    (∃ c : Fin n,
      c ∉ retainedActive C u ∧
      c ∉ retainedActive C v)
    ∨
    (∃ c : Fin n,
      c ∉ residualForbidden C u v ∧
      c ∈ outgoingRetained C u ∧
      c ∉ retainedActive C v) := by
  obtain ⟨c, hsafeC, hinactive⟩ :=
    exists_safe_inactive_coordinate_of_safe_overlap
      C huWord hvWord hsafe
  rcases hinactive with hcu | hcv
  · left
    exact ⟨c, hcu,
      safe_colour_common_inactive_of_sameRetained_lower
        C hsame hsafeC hcu⟩
  · rcases safe_upper_inactive_lower_inactive_or_outgoing
      C hsafeC hcv with hcu | hOut
    · left
      exact ⟨c, hcu, hcv⟩
    · right
      exact ⟨c, hsafeC, hOut, hcv⟩

/-- Every hard overlap pair is therefore in one of three sharply described
branches: common inactive, oriented safe exception, or unsafe. -/
theorem sameRetained_overlap_trichotomy
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (hsame : SameRetained C u v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v) :
    (∃ c : Fin n,
      c ∉ retainedActive C u ∧
      c ∉ retainedActive C v)
    ∨
    (∃ c : Fin n,
      c ∉ residualForbidden C u v ∧
      c ∈ outgoingRetained C u ∧
      c ∉ retainedActive C v)
    ∨
    (¬ ∃ c : Fin n, c ∉ residualForbidden C u v) := by
  by_cases hsafe :
      ∃ c : Fin n, c ∉ residualForbidden C u v
  · rcases safe_sameRetained_overlap_commonInactive_or_oriented
      C hsame huWord hvWord hsafe with hcommon | horiented
    · exact Or.inl hcommon
    · exact Or.inr (Or.inl horiented)
  · exact Or.inr (Or.inr hsafe)

#print axioms safe_colour_common_inactive_of_sameRetained_lower
#print axioms safe_upper_inactive_lower_inactive_or_outgoing
#print axioms safe_sameRetained_overlap_commonInactive_or_oriented
#print axioms sameRetained_overlap_trichotomy

end OrderedEdgeColoring
end JSP000404Research
