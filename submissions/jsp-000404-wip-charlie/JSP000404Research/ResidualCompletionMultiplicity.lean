
import JSP000404Research.ResidualCompletionIntersection
import JSP000404Research.ResidualInactiveUniqueCode
import Mathlib.Tactic

/-!
# Retained completion cubes have multiplicity at most two

Project the canonical (n+1)-colour partial-code system to its first n retained
coordinates.

If retained completion cubes of two ordered vertices u<v intersect, their
joining edge cannot have a retained colour: that retained edge colour would
be active at both endpoints and the canonical retained bits would disagree,
while a common completion word would have to agree with both.

Hence every nontrivial projected-cube overlap lies on a residual edge.

Moreover, a single retained word cannot lie in the completion cubes of three
distinct vertices.  Indeed every pair among them would be a residual edge,
so on three linearly ordered vertices the two consecutive edges would both be
residual, contradicting the ordered-colouring axiom.

Thus the entire projected completion family has pointwise multiplicity at most
two.  The remaining weighted problem is therefore a pairwise-overlap defect
problem, not a general higher-order inclusion-exclusion problem.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- An overlap of retained completion cubes on an increasing pair forces the
joining edge to be residual. -/
theorem isResidual_of_retainedCompletion_overlap_lt
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (huv : u < v)
    {word : Fin n → Bool}
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v) :
    IsResidual C u v := by
  intro hret
  let c : Fin n := retainedColor C u v hret
  have hcu :
      c ∈ retainedActive C u :=
    retainedColor_mem_retainedActive_left
      C huv hret
  have hcv :
      c ∈ retainedActive C v :=
    retainedColor_mem_retainedActive_right
      C huv hret
  have huComp :
      RetainedCompletes C u word :=
    (mem_retainedCompletionWords C u word).1 hu
  have hvComp :
      RetainedCompletes C v word :=
    (mem_retainedCompletionWords C v word).1 hv
  have hbu :
      word c = retainedBit C u c :=
    huComp c hcu
  have hbv :
      word c = retainedBit C v c :=
    hvComp c hcv
  have hne :
      retainedBit C u c ≠ retainedBit C v c :=
    retainedBit_ne_of_retained_edge
      C huv hret
  exact hne (hbu.symm.trans hbv)

/-- Symmetric unordered form: any common retained completion of distinct
vertices forces their connecting increasing edge to be residual. -/
theorem retainedCompletion_overlap_forces_residual
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (huv : u ≠ v)
    {word : Fin n → Bool}
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v) :
    (u < v ∧ IsResidual C u v) ∨
      (v < u ∧ IsResidual C v u) := by
  rcases lt_or_gt_of_ne huv with huvlt | hvult
  · exact Or.inl ⟨huvlt,
      isResidual_of_retainedCompletion_overlap_lt
        C huvlt hu hv⟩
  · exact Or.inr ⟨hvult,
      isResidual_of_retainedCompletion_overlap_lt
        C hvult hv hu⟩

/-- No retained completion word can belong to three pairwise-distinct
vertices. -/
theorem no_three_distinct_share_retained_completion
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a b c : V}
    (hab : a ≠ b)
    (hac : a ≠ c)
    (hbc : b ≠ c)
    {word : Fin n → Bool}
    (ha : word ∈ retainedCompletionWords C a)
    (hb : word ∈ retainedCompletionWords C b)
    (hc : word ∈ retainedCompletionWords C c) :
    False := by
  rcases lt_trichotomy a b with hablt | habEq | hbalt
  · rcases lt_trichotomy b c with hbclt | hbcEq | hcblt
    · have hresAB :=
        isResidual_of_retainedCompletion_overlap_lt
          C hablt ha hb
      have hresBC :=
        isResidual_of_retainedCompletion_overlap_lt
          C hbclt hb hc
      exact no_two_residual_on_path
        C hablt hbclt hresAB hresBC
    · exact hbc hbcEq
    · rcases lt_trichotomy a c with haclt | hacEq | hcalt
      · have hresAC :=
          isResidual_of_retainedCompletion_overlap_lt
            C haclt ha hc
        have hresCB :=
          isResidual_of_retainedCompletion_overlap_lt
            C hcblt hc hb
        exact no_two_residual_on_path
          C haclt hcblt hresAC hresCB
      · exact hac hacEq
      · have hresCA :=
          isResidual_of_retainedCompletion_overlap_lt
            C hcalt hc ha
        have hresAB :=
          isResidual_of_retainedCompletion_overlap_lt
            C hablt ha hb
        exact no_two_residual_on_path
          C hcalt hablt hresCA hresAB
  · exact hab habEq
  · rcases lt_trichotomy a c with haclt | hacEq | hcalt
    · have hresBA :=
        isResidual_of_retainedCompletion_overlap_lt
          C hbalt hb ha
      have hresAC :=
        isResidual_of_retainedCompletion_overlap_lt
          C haclt ha hc
      exact no_two_residual_on_path
        C hbalt haclt hresBA hresAC
    · exact hac hacEq
    · rcases lt_trichotomy b c with hbclt | hbcEq | hcblt
      · have hresBC :=
          isResidual_of_retainedCompletion_overlap_lt
            C hbclt hb hc
        have hresCA :=
          isResidual_of_retainedCompletion_overlap_lt
            C hcalt hc ha
        exact no_two_residual_on_path
          C hbclt hcalt hresBC hresCA
      · exact hbc hbcEq
      · have hresCB :=
          isResidual_of_retainedCompletion_overlap_lt
            C hcblt hc hb
        have hresBA :=
          isResidual_of_retainedCompletion_overlap_lt
            C hbalt hb ha
        exact no_two_residual_on_path
          C hcblt hbalt hresCB hresBA

/-- Set-level multiplicity statement: among vertices whose retained completion
cube contains a fixed word, any three must contain a collision. -/
theorem three_completion_members_force_vertex_collision
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (word : Fin n → Bool)
    (a b c : V)
    (ha : word ∈ retainedCompletionWords C a)
    (hb : word ∈ retainedCompletionWords C b)
    (hc : word ∈ retainedCompletionWords C c) :
    a = b ∨ a = c ∨ b = c := by
  by_contra h
  push_neg at h
  exact no_three_distinct_share_retained_completion
    C h.1 h.2.1 h.2.2 ha hb hc

/-- An exact projected-loss vertex has a retained completion cube disjoint
from every other vertex: projected loss forces residual inactivity, whereas
any nontrivial overlap would force a residual edge incident to it. -/
theorem exact_projected_loss_completion_disjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {r : ℕ} {v w : V}
    (hv :
      v ∈ layerLossSet exponent (projectedFree C) r)
    (hvw : v ≠ w) :
    Disjoint
      (retainedCompletionWords C v)
      (retainedCompletionWords C w) := by
  classical
  rw [Finset.disjoint_left]
  intro word hvWord hwWord
  have hinactive :=
    residual_inactive_of_mem_layerLoss_projected
      C exponent hexp honeLoss hv
  rcases retainedCompletion_overlap_forces_residual
      C hvw hvWord hwWord with hres | hres
  · exact hinactive
      (residualCoord_mem_active_of_isResidual
        C hres.1 hres.2).1
  · exact hinactive
      (residualCoord_mem_active_of_isResidual
        C hres.1 hres.2).2

#print axioms isResidual_of_retainedCompletion_overlap_lt
#print axioms retainedCompletion_overlap_forces_residual
#print axioms no_three_distinct_share_retained_completion
#print axioms three_completion_members_force_vertex_collision
#print axioms exact_projected_loss_completion_disjoint

end OrderedEdgeColoring
end JSP000404Research
