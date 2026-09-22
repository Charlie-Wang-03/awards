import JSP000404Research.ResidualHoleInjection
import JSP000404Research.RetainedOrientation
import Mathlib.Tactic

/-!
# Hard residual pairs cannot be safely absorbed at the upper endpoint

Let u<v be a hard retained-code collision: u and v have the same first n
canonical bits.

For a retained colour c, equality of retained bits means that c is incoming at
u iff it is incoming at v.

A locally safe recolouring target for the residual edge u--v must avoid

  incomingRetained(u) union outgoingRetained(v).

Therefore it is not incoming at u, hence not incoming at v.  If it were already
retained-active at v, the incoming/outgoing decomposition would force it to be
outgoing at v, contradicting local safety.

So every locally safe target for a hard residual pair is necessarily a NEW
retained-active colour at the upper endpoint.

This formally closes the naive "safe and absorbed at both endpoints" branch.
Any exact-budget treatment of a saturated upper endpoint must use a genuinely
different mechanism such as component flips or Boolean-code displacement.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Membership in the incoming retained-colour set is exactly truth of the
canonical retained bit. -/
theorem mem_incomingRetained_iff_retainedBit_true
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (c : Fin n) :
    c ∈ incomingRetained C v ↔
      retainedBit C v c = true := by
  rw [mem_incomingRetained_iff]
  unfold retainedBit
  exact (bit_eq_true_iff C v c.castSucc).symm

/-- Vertices with the same retained code have identical incoming-colour
membership for every retained coordinate. -/
theorem incomingRetained_mem_iff_of_sameRetained
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hsame : SameRetained C u v)
    (c : Fin n) :
    c ∈ incomingRetained C u ↔
      c ∈ incomingRetained C v := by
  rw [mem_incomingRetained_iff_retainedBit_true,
      mem_incomingRetained_iff_retainedBit_true]
  exact eq_iff_iff.mpr (hsame c)

/-- A colour outside the exact forbidden list is absent from incoming colours
at the lower endpoint and outgoing colours at the upper endpoint. -/
theorem not_forbidden_gives_endpoint_absences
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {c : Fin n}
    (hsafe : c ∉ residualForbidden C u v) :
    c ∉ incomingRetained C u ∧
      c ∉ outgoingRetained C v := by
  constructor
  · intro h
    exact hsafe (Finset.mem_union_left _ h)
  · intro h
    exact hsafe (Finset.mem_union_right _ h)

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
  have habs :=
    not_forbidden_gives_endpoint_absences C hsafe
  have hnotInU : c ∉ incomingRetained C u := habs.1
  have hnotOutV : c ∉ outgoingRetained C v := habs.2
  have hnotInV : c ∉ incomingRetained C v := by
    intro hInV
    exact hnotInU
      ((incomingRetained_mem_iff_of_sameRetained
        C hsame c).2 hInV)
  rw [retainedActive_eq_incoming_union_outgoing C v]
  intro hactive
  rw [Finset.mem_union] at hactive
  rcases hactive with hInV | hOutV
  · exact hnotInV hInV
  · exact hnotOutV hOutV

/-- In particular there is no retained colour which is simultaneously a safe
target for a hard pair and already active at both endpoints. -/
theorem no_safe_common_absorbed_colour_of_sameRetained
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hsame : SameRetained C u v) :
    ¬ ∃ c : Fin n,
      c ∉ residualForbidden C u v ∧
      c ∈ retainedActive C u ∧
      c ∈ retainedActive C v := by
  rintro ⟨c, hsafe, _hactiveU, hactiveV⟩
  exact
    (safe_target_not_retainedActive_upper_of_sameRetained
      C hsame hsafe) hactiveV

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

#print axioms mem_incomingRetained_iff_retainedBit_true
#print axioms incomingRetained_mem_iff_of_sameRetained
#print axioms safe_target_not_retainedActive_upper_of_sameRetained
#print axioms no_safe_common_absorbed_colour_of_sameRetained
#print axioms safe_target_not_retainedActive_upper_of_hardResidual

end OrderedEdgeColoring
end JSP000404Research
