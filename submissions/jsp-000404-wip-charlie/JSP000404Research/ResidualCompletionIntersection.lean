
import JSP000404Research.ResidualSameCodeOrientation
import JSP000404Research.WeightedHansel
import Mathlib.Tactic

/-!
# Exact intersection of retained partial-code cubes in a light duplicate fibre

For a vertex v, the retained partial Boolean word specifies precisely the
coordinates in retainedActive(C,v), with canonical values retainedBit(C,v).

Let u,v have the same retained base code.  If they have no common inactive
retained coordinate, then

  retainedActive(u) union retainedActive(v) = all retained coordinates.

Hence any complete n-bit word compatible with both retained partial words is
forced coordinate-by-coordinate to equal their common retained base code.

Therefore the two retained completion subcubes intersect in exactly one point.

This is the set-theoretic refinement of the positive light-fibre dyadic
estimate.  The only internal collision of the two partial cubes is their
common base word.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

def RetainedCompletes
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V)
    (word : Fin n → Bool) : Prop :=
  ∀ c, c ∈ retainedActive C v →
    word c = retainedBit C v c

noncomputable def retainedCompletionWords
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) : Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.filter (RetainedCompletes C v)

@[simp] theorem mem_retainedCompletionWords
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (word : Fin n → Bool) :
    word ∈ retainedCompletionWords C v ↔
      RetainedCompletes C v word := by
  classical
  simp [retainedCompletionWords]

/-- No common inactive coordinate means the two retained active sets cover all
retained coordinates. -/
theorem retainedActive_union_eq_univ_of_no_common_inactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hno :
      ¬ ∃ c : Fin n,
        c ∉ retainedActive C u ∧
        c ∉ retainedActive C v) :
    retainedActive C u ∪ retainedActive C v =
      (Finset.univ : Finset (Fin n)) := by
  classical
  apply Finset.eq_univ_of_forall
  intro c
  by_contra hc
  have hc' : c ∉ retainedActive C u ∪ retainedActive C v := hc
  rw [Finset.mem_union] at hc'
  push_neg at hc'
  exact hno ⟨c, hc'.1, hc'.2⟩

/-- The common retained base code completes both members of a same-retained
pair. -/
theorem retained_base_mem_both_completionWords
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hsame : SameRetained C u v) :
    (fun c => retainedBit C u c) ∈
        retainedCompletionWords C u ∩
          retainedCompletionWords C v := by
  classical
  rw [Finset.mem_inter]
  constructor
  · apply (mem_retainedCompletionWords C u _).2
    intro c hc
    rfl
  · apply (mem_retainedCompletionWords C v _).2
    intro c hc
    exact hsame c

/-- Any common completion is the common retained base code. -/
theorem common_retained_completion_eq_base
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hsame : SameRetained C u v)
    (hno :
      ¬ ∃ c : Fin n,
        c ∉ retainedActive C u ∧
        c ∉ retainedActive C v)
    {word : Fin n → Bool}
    (hu : RetainedCompletes C u word)
    (hv : RetainedCompletes C v word) :
    word = fun c => retainedBit C u c := by
  funext c
  have hcover :
      c ∈ retainedActive C u ∨
        c ∈ retainedActive C v := by
    have hall :=
      retainedActive_union_eq_univ_of_no_common_inactive
        C hno
    have hc :
        c ∈ retainedActive C u ∪ retainedActive C v := by
      rw [hall]
      simp
    simpa [Finset.mem_union] using hc
  rcases hcover with hcu | hcv
  · exact hu c hcu
  · exact (hv c hcv).trans (hsame c).symm

/-- Exact singleton intersection of the two retained completion cubes. -/
theorem retainedCompletionWords_inter_eq_singleton
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hsame : SameRetained C u v)
    (hno :
      ¬ ∃ c : Fin n,
        c ∉ retainedActive C u ∧
        c ∉ retainedActive C v) :
    retainedCompletionWords C u ∩
        retainedCompletionWords C v =
      {fun c => retainedBit C u c} := by
  classical
  apply Finset.ext
  intro word
  constructor
  · intro hw
    have hu :
        RetainedCompletes C u word :=
      (mem_retainedCompletionWords C u word).1
        (Finset.mem_inter.mp hw).1
    have hv :
        RetainedCompletes C v word :=
      (mem_retainedCompletionWords C v word).1
        (Finset.mem_inter.mp hw).2
    have heq :=
      common_retained_completion_eq_base
        C hsame hno hu hv
    simpa [heq]
  · intro hw
    have heq :
        word = fun c => retainedBit C u c := by
      simpa using hw
    subst word
    exact retained_base_mem_both_completionWords
      C hsame

/-- Consequently the overlap cardinality is exactly one. -/
theorem retainedCompletionWords_inter_card_eq_one
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hsame : SameRetained C u v)
    (hno :
      ¬ ∃ c : Fin n,
        c ∉ retainedActive C u ∧
        c ∉ retainedActive C v) :
    (retainedCompletionWords C u ∩
      retainedCompletionWords C v).card = 1 := by
  rw [retainedCompletionWords_inter_eq_singleton
    C hsame hno]
  simp

/-- Union cardinality loses exactly the one common base code. -/
theorem retainedCompletionWords_union_card
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hsame : SameRetained C u v)
    (hno :
      ¬ ∃ c : Fin n,
        c ∉ retainedActive C u ∧
        c ∉ retainedActive C v) :
    (retainedCompletionWords C u ∪
      retainedCompletionWords C v).card + 1 =
        (retainedCompletionWords C u).card +
          (retainedCompletionWords C v).card := by
  have hcard :=
    Finset.card_union_add_card_inter
      (retainedCompletionWords C u)
      (retainedCompletionWords C v)
  rw [retainedCompletionWords_inter_card_eq_one
    C hsame hno] at hcard
  omega

#print axioms retainedActive_union_eq_univ_of_no_common_inactive
#print axioms common_retained_completion_eq_base
#print axioms retainedCompletionWords_inter_eq_singleton
#print axioms retainedCompletionWords_inter_card_eq_one
#print axioms retainedCompletionWords_union_card

end OrderedEdgeColoring
end JSP000404Research
