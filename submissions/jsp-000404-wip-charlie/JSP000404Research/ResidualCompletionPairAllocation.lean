import JSP000404Research.ResidualCompletionAccounting
import JSP000404Research.ResidualCompletionMultiplicity
import Mathlib.Tactic

/-!
# Unique residual-pair ownership of overlapping completion words

Every retained completion word belongs to at most two vertices.
Consequently an overlap word cannot belong to two different
*unordered* vertex pairs, and, with ordered endpoints, the owner
pair is unique. Pair intersection sets for different ordered edges
are disjoint.

This makes global overlap accounting by residual edges rigorous.
It does not yet give a geometric injection from these paid overlaps
to Boolean holes, surplus, or compensated projected loss.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- If an n-bit word completes distinct u,v, then no third vertex
can have it in its completion cube. -/
theorem completion_word_pair_covers_only_endpoints
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {word : Fin n → Bool}
    (huv : u ≠ v)
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v)
    (hw : word ∈ retainedCompletionWords C w) :
    w = u ∨ w = v := by
  by_cases hwu : w = u
  · exact Or.inl hwu
  by_cases hwv : w = v
  · exact Or.inr hwv
  exact False.elim
    (no_three_distinct_share_retained_completion
      C huv (Ne.symm hwu) (Ne.symm hwv) hu hv hw)

/-- An overlapping completion word determines its increasing
pair of covering vertices uniquely, without choice of witnesses. -/
theorem completion_word_unique_ordered_pair
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v a b : V} {word : Fin n → Bool}
    (huv : u < v)
    (hab : a < b)
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v)
    (ha : word ∈ retainedCompletionWords C a)
    (hb : word ∈ retainedCompletionWords C b) :
    u = a ∧ v = b := by
  have ha' : a = u ∨ a = v :=
    completion_word_pair_covers_only_endpoints
      C (ne_of_lt huv) hu hv ha
  have hb' : b = u ∨ b = v :=
    completion_word_pair_covers_only_endpoints
      C (ne_of_lt huv) hu hv hb
  rcases ha' with hau | hav
  · rcases hb' with hbu | hbv
    · subst a
      subst b
      exact False.elim (lt_irrefl u hab)
    · exact ⟨hau.symm, hbv.symm⟩
  · rcases hb' with hbu | hbv
    · subst a
      subst b
      exact False.elim (lt_asymm huv hab)
    · subst a
      subst b
      exact False.elim (lt_irrefl v hab)

/-- Each vertex pair's completion-intersection set is disjoint
from that of a DIFFERENT increasing vertex pair.

In particular, global pairwise-overlap weights never double-count
a Boolean word between different residual edges. -/
theorem retained_completion_pair_intersections_disjoint
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v a b : V}
    (huv : u < v)
    (hab : a < b)
    (hdiff : u ≠ a ∨ v ≠ b) :
    Disjoint
      (retainedCompletionWords C u ∩ retainedCompletionWords C v)
      (retainedCompletionWords C a ∩ retainedCompletionWords C b) := by
  classical
  rw [Finset.disjoint_left]
  intro word hUV hAB
  obtain ⟨hua, hvb⟩ :=
    completion_word_unique_ordered_pair
      C huv hab
      (Finset.mem_inter.mp hUV).1
      (Finset.mem_inter.mp hUV).2
      (Finset.mem_inter.mp hAB).1
      (Finset.mem_inter.mp hAB).2
  rcases hdiff with hd | hd
  · exact hd hua
  · exact hd hvb

/-- Any nonempty pairwise completion intersection occurs on a
residual edge, not on an edge using a retained colour. -/
theorem nonempty_retained_completion_pair_forces_residual
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (huv : u < v)
    (hinter :
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).Nonempty) :
    IsResidual C u v := by
  obtain ⟨word, hw⟩ := hinter
  exact isResidual_of_retainedCompletion_overlap_lt
    C huv (Finset.mem_inter.mp hw).1
      (Finset.mem_inter.mp hw).2

#print axioms completion_word_pair_covers_only_endpoints
#print axioms completion_word_unique_ordered_pair
#print axioms retained_completion_pair_intersections_disjoint
#print axioms nonempty_retained_completion_pair_forces_residual

end OrderedEdgeColoring
end JSP000404Research
