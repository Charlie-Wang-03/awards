import JSP000404Research.ResidualCompletionMultiplicity
import Mathlib.Tactic

/-!
# Bipartite orientation of the residual-overlap carrier graph

Every nontrivial retained-completion overlap is carried by a residual edge.
The ordered-colouring axiom forbids two residual edges on an increasing
two-edge path.

Consequently no vertex can simultaneously be the upper endpoint of one
residual-overlap edge and the lower endpoint of another. The carrier graph is
therefore canonically bipartite: vertices may act as residual sources, as
residual sinks, or as neither, but never as both.

This global orientation constraint is independent of the Boolean displacement
chosen later and will be used to restrict possible augmenting cycles.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

def IsResidualSource
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) : Prop :=
  ∃ w, v < w ∧ IsResidual C v w

def IsResidualSink
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) : Prop :=
  ∃ u, u < v ∧ IsResidual C u v

theorem residualSource_not_sink
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V}
    (hsrc : IsResidualSource C v) :
    ¬ IsResidualSink C v := by
  rintro ⟨u,huv,hresUV⟩
  obtain ⟨w,hvw,hresVW⟩ := hsrc
  exact no_two_residual_on_path
    C huv hvw hresUV hresVW

theorem residualSink_not_source
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V}
    (hsink : IsResidualSink C v) :
    ¬ IsResidualSource C v := by
  intro hsrc
  exact residualSource_not_sink C hsrc hsink

theorem overlap_left_is_residualSource
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (huv : u < v)
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v) :
    IsResidualSource C u := by
  exact ⟨v,huv,
    isResidual_of_retainedCompletion_overlap_lt
      C huv hu hv⟩

theorem overlap_right_is_residualSink
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (huv : u < v)
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v) :
    IsResidualSink C v := by
  exact ⟨u,huv,
    isResidual_of_retainedCompletion_overlap_lt
      C huv hu hv⟩

theorem overlap_left_not_residualSink
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (huv : u < v)
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v) :
    ¬ IsResidualSink C u := by
  exact residualSource_not_sink C
    (overlap_left_is_residualSource C huv hu hv)

theorem overlap_right_not_residualSource
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (huv : u < v)
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v) :
    ¬ IsResidualSource C v := by
  exact residualSink_not_source C
    (overlap_right_is_residualSink C huv hu hv)

#print axioms residualSource_not_sink
#print axioms overlap_left_not_residualSink
#print axioms overlap_right_not_residualSource

end OrderedEdgeColoring
end JSP000404Research
