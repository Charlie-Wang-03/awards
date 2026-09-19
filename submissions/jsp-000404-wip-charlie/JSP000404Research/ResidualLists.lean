import JSP000404Research.ResidualSafeTarget
import Mathlib.Tactic

/-!
# Local forbidden lists for the residual colour

For a residual edge `u<v`, safety after recolouring only forbids

* retained colours used on incoming edges at `u`, and
* retained colours used on outgoing edges at `v`.

The union of these two finite sets is the exact local forbidden list.  If its
cardinality is strictly below `k`, some colour of `Fin k` is available, and
that colour is automatically a compatible target in the sense of
`ResidualTargetCompatible`.

Thus the safety part of residual-colour elimination is reduced to the concrete
local inequality

  card (incomingRetained u ∪ outgoingRetained v) < k.

The separate active-colour budget is intentionally not hidden here.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Retained colours entering a vertex. -/
noncomputable def incomingRetained
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1)) (v : V) :
    Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun c =>
    ∃ a, a < v ∧ C.color a v = c.castSucc

/-- Retained colours leaving a vertex. -/
noncomputable def outgoingRetained
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1)) (v : V) :
    Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun c =>
    ∃ w, v < w ∧ C.color v w = c.castSucc

/-- Exact set of retained colours forbidden as targets for a residual edge. -/
noncomputable def residualForbidden
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1)) (u v : V) :
    Finset (Fin k) :=
  incomingRetained C u ∪ outgoingRetained C v

theorem mem_incomingRetained_iff
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1)) (v : V) (c : Fin k) :
    c ∈ incomingRetained C v ↔
      ∃ a, a < v ∧ C.color a v = c.castSucc := by
  classical
  simp [incomingRetained]

theorem mem_outgoingRetained_iff
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1)) (v : V) (c : Fin k) :
    c ∈ outgoingRetained C v ↔
      ∃ w, v < w ∧ C.color v w = c.castSucc := by
  classical
  simp [outgoingRetained]

/-- A proper-cardinality subset of `Fin k` misses at least one colour. -/
theorem exists_fin_not_mem_of_card_lt
    {k : ℕ} (s : Finset (Fin k))
    (hcard : s.card < k) :
    ∃ c : Fin k, c ∉ s := by
  classical
  by_contra h
  push_neg at h
  have hsub : (Finset.univ : Finset (Fin k)) ⊆ s := by
    intro c hc
    exact h c
  have hc := Finset.card_le_card hsub
  have hk : k ≤ s.card := by
    simpa using hc
  omega

/-- Avoiding the local forbidden list is exactly enough for all mixed
retained/residual two-path conflicts at this edge. -/
theorem compatible_target_of_not_mem_forbidden
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1))
    {u v : V} (c : Fin k)
    (hc : c ∉ residualForbidden C u v) :
    (∀ {a : V} (hau : a < u)
        (haRet : (C.color a u).val < k),
      c ≠ retainedColor C a u haRet) ∧
    (∀ {w : V} (hvw : v < w)
        (hwRet : (C.color v w).val < k),
      c ≠ retainedColor C v w hwRet) := by
  constructor
  · intro a hau haRet heq
    apply hc
    apply Finset.mem_union_left
    apply (mem_incomingRetained_iff C u c).2
    refine ⟨a, hau, ?_⟩
    apply Fin.ext
    have hval := congrArg Fin.val heq
    simpa [retainedColor] using hval.symm
  · intro w hvw hwRet heq
    apply hc
    apply Finset.mem_union_right
    apply (mem_outgoingRetained_iff C v c).2
    refine ⟨w, hvw, ?_⟩
    apply Fin.ext
    have hval := congrArg Fin.val heq
    simpa [retainedColor] using hval.symm

/-- The local forbidden-cardinality inequality produces a compatible target
colour for one residual edge. -/
theorem exists_compatible_target_of_forbidden_card_lt
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1))
    {u v : V}
    (hcard : (residualForbidden C u v).card < k) :
    ∃ c : Fin k,
      (∀ {a : V} (hau : a < u)
          (haRet : (C.color a u).val < k),
        c ≠ retainedColor C a u haRet) ∧
      (∀ {w : V} (hvw : v < w)
          (hwRet : (C.color v w).val < k),
        c ≠ retainedColor C v w hwRet) := by
  obtain ⟨c, hc⟩ :=
    exists_fin_not_mem_of_card_lt (residualForbidden C u v) hcard
  exact ⟨c, compatible_target_of_not_mem_forbidden C c hc⟩

#print axioms exists_fin_not_mem_of_card_lt
#print axioms compatible_target_of_not_mem_forbidden
#print axioms exists_compatible_target_of_forbidden_card_lt

end OrderedEdgeColoring
end JSP000404Research
