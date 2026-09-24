
import JSP000404Research.ResidualOverlapDichotomy
import JSP000404Research.ResidualSameCodeOrientation
import Mathlib.Tactic

/-!
# Safe colours on hard residual pairs are common inactive

For a hard residual pair u,v with the same canonical retained code, a locally
safe retained colour c avoids

  incomingRetained(u) union outgoingRetained(v).

Suppose c is inactive at u.  Then its canonical retained bit at u is false,
hence also false at v by SameRetained.  If c were active at v, false bit means
it is outgoing at v, contradicting safety.  Thus c is inactive at v as well.

Symmetrically, inactivity at v forces inactivity at u.

Therefore on a SameRetained pair,

  safe + inactive at one endpoint
    => common inactive.

For overlap carriers ResidualOverlapDichotomy already says every safe colour
is inactive at at least one endpoint.  Hence a safe hard overlap pair always
has a common inactive coordinate and falls directly into the Boolean-hole
repair regime.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem safe_colour_common_inactive_of_sameRetained_left
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

theorem safe_colour_common_inactive_of_sameRetained_right
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hsame : SameRetained C u v)
    {c : Fin n}
    (hsafe : c ∉ residualForbidden C u v)
    (hcv : c ∉ retainedActive C v) :
    c ∉ retainedActive C u := by
  intro hcu
  have hvFalse :
      retainedBit C v c = false :=
    retainedBit_false_of_retained_inactive C hcv
  have huFalse :
      retainedBit C u c = false := by
    rw [hsame c]
    exact hvFalse
  rw [retainedActive_eq_incoming_union_outgoing C u] at hcu
  rcases Finset.mem_union.mp hcu with hIn | hOut
  · exact hsafe (Finset.mem_union_left _ hIn)
  · have huNotIn :
        c ∉ incomingRetained C u := by
      exact Finset.disjoint_left.mp
        (incomingRetained_disjoint_outgoingRetained C u)
        · exact fun h => h
        · exact hOut
    have huFalse' :
        retainedBit C u c = false := by
      unfold retainedBit
      apply bit_eq_false_iff.mpr
      intro hex
      exact huNotIn
        ((mem_incomingRetained_iff C u c).2 hex)
    exact False.elim (by
      have := huFalse.trans huFalse'.symm
      simp at this)

/-- Cleaner symmetric package: on a same-retained pair, a safe colour is
inactive at one endpoint iff it is inactive at the other. -/
theorem safe_colour_inactive_iff_of_sameRetained
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hsame : SameRetained C u v)
    {c : Fin n}
    (hsafe : c ∉ residualForbidden C u v) :
    (c ∉ retainedActive C u) ↔
      (c ∉ retainedActive C v) := by
  constructor
  · exact safe_colour_common_inactive_of_sameRetained_left
      C hsame hsafe
  · exact safe_colour_common_inactive_of_sameRetained_right
      C hsame hsafe

/-- A safe hard overlap pair always exposes a common inactive coordinate. -/
theorem safe_sameRetained_overlap_has_common_inactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (hsame : SameRetained C u v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hsafe :
      ∃ c : Fin n, c ∉ residualForbidden C u v) :
    ∃ c : Fin n,
      c ∉ retainedActive C u ∧
      c ∉ retainedActive C v := by
  obtain ⟨c, hsafeC, hinactive⟩ :=
    exists_safe_inactive_coordinate_of_safe_overlap
      C huWord hvWord hsafe
  refine ⟨c, ?_⟩
  rcases hinactive with hcu | hcv
  · exact ⟨hcu,
      safe_colour_common_inactive_of_sameRetained_left
        C hsame hsafeC hcu⟩
  · exact ⟨
      safe_colour_common_inactive_of_sameRetained_right
        C hsame hsafeC hcv,
      hcv⟩

/-- Therefore every hard overlap pair either has a common inactive repair
coordinate or is unsafe. -/
theorem sameRetained_overlap_commonInactive_or_unsafe
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
    (¬ ∃ c : Fin n, c ∉ residualForbidden C u v) := by
  by_cases hsafe :
      ∃ c : Fin n, c ∉ residualForbidden C u v
  · exact Or.inl
      (safe_sameRetained_overlap_has_common_inactive
        C hsame huWord hvWord hsafe)
  · exact Or.inr hsafe

#print axioms safe_colour_common_inactive_of_sameRetained_left
#print axioms safe_colour_inactive_iff_of_sameRetained
#print axioms safe_sameRetained_overlap_has_common_inactive
#print axioms sameRetained_overlap_commonInactive_or_unsafe

end OrderedEdgeColoring
end JSP000404Research
