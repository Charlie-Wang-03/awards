import JSP000404Research.ResidualHoleInjection
import JSP000404Research.RetainedOrientation
import Mathlib.Tactic

/-!
# Orientation rigidity inside a retained-code fibre

For the canonical retained code, one bit records whether a retained colour is
incoming at the vertex.  Hence two vertices with the same retained Boolean
code have exactly the same incoming-retained colour set.

This has an important consequence for residual elimination.  Let u<v be a
hard vertical pair with the same retained code.  A retained target colour is
locally safe for the residual edge only if it avoids

  incomingRetained(u) union outgoingRetained(v).

If that target were already active at both endpoints, then at u it would have
to be outgoing (because it is not incoming), while at v it would have to be
incoming (because it is not outgoing).  But the incoming sets of u and v are
equal, and incoming/outgoing colours are disjoint at u.  Contradiction.

Thus a hard retained-code collision can never be repaired by a target which
is simultaneously

* locally safe, and
* absorbed at both endpoints.

Zero-palette-growth residual recolouring therefore cannot solve the genuinely
hard fibres.  The remaining mechanisms are component reorientation or Boolean
hole/displacement repairs.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Retained incoming-colour membership is exactly the retained canonical bit
being true. -/
theorem mem_incomingRetained_iff_retainedBit_true
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (c : Fin n) :
    c ∈ incomingRetained C v ↔
      retainedBit C v c = true := by
  rw [mem_incomingRetained_iff]
  unfold retainedBit
  exact (bit_eq_true_iff C v c.castSucc).symm

/-- Same retained Boolean code forces equality of the incoming retained sets. -/
theorem incomingRetained_eq_of_sameRetained
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hsame : SameRetained C u v) :
    incomingRetained C u = incomingRetained C v := by
  classical
  ext c
  rw [mem_incomingRetained_iff_retainedBit_true,
      mem_incomingRetained_iff_retainedBit_true]
  exact congrArg (fun b => b = true) (hsame c)

/-- For a same-retained pair, an outgoing colour at u cannot be incoming at v. -/
theorem outgoing_disjoint_incoming_of_sameRetained
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hsame : SameRetained C u v) :
    Disjoint (outgoingRetained C u) (incomingRetained C v) := by
  rw [← incomingRetained_eq_of_sameRetained C hsame]
  exact (incomingRetained_disjoint_outgoingRetained C u).symm

/-- A locally safe target for a same-retained residual pair cannot already be
active at both endpoints. -/
theorem safe_target_not_absorbed_both_of_sameRetained
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hsame : SameRetained C u v)
    {c : Fin n}
    (hsafe : c ∉ residualForbidden C u v) :
    ¬ (c ∈ retainedActive C u ∧
       c ∈ retainedActive C v) := by
  classical
  intro hboth
  have hnotInU : c ∉ incomingRetained C u := by
    intro hc
    apply hsafe
    exact Finset.mem_union_left _ hc
  have hnotOutV : c ∉ outgoingRetained C v := by
    intro hc
    apply hsafe
    exact Finset.mem_union_right _ hc
  rw [retainedActive_eq_incoming_union_outgoing C u] at hboth
  rw [retainedActive_eq_incoming_union_outgoing C v] at hboth
  have hOutU : c ∈ outgoingRetained C u := by
    rcases Finset.mem_union.mp hboth.1 with hIn | hOut
    · exact False.elim (hnotInU hIn)
    · exact hOut
  have hInV : c ∈ incomingRetained C v := by
    rcases Finset.mem_union.mp hboth.2 with hIn | hOut
    · exact hIn
    · exact False.elim (hnotOutV hOut)
  exact Finset.disjoint_left.mp
    (outgoing_disjoint_incoming_of_sameRetained C hsame)
    hOutU hInV

/-- In particular, no safe residual target can satisfy the old full-absorption
condition on a hard same-retained edge. -/
theorem no_safe_absorbed_target_of_sameRetained
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hsame : SameRetained C u v) :
    ¬ ∃ c : Fin n,
      c ∉ residualForbidden C u v ∧
      c ∈ retainedActive C u ∧
      c ∈ retainedActive C v := by
  rintro ⟨c, hsafe, hcu, hcv⟩
  exact safe_target_not_absorbed_both_of_sameRetained
    C hsame hsafe ⟨hcu, hcv⟩

#print axioms mem_incomingRetained_iff_retainedBit_true
#print axioms incomingRetained_eq_of_sameRetained
#print axioms outgoing_disjoint_incoming_of_sameRetained
#print axioms safe_target_not_absorbed_both_of_sameRetained
#print axioms no_safe_absorbed_target_of_sameRetained

end OrderedEdgeColoring
end JSP000404Research
