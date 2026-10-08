import JSP000404Research.ResidualLossTranslatedBlock
import Mathlib.Tactic

/-!
# Pairwise disjoint translated slices at one owner

Fix a vertex v and two distinct retained-active coordinates c,d.
The translated completion cubes

  T_c = flip_c(Q_v),
  T_d = flip_d(Q_v)

are disjoint.

Indeed, if y belonged to both, then flip_c(y) and flip_d(y) would both lie in
Q_v.  Since c is active at v, both source words must have the canonical c-bit.
But flip_c(y) changes c while flip_d(y) does not, forcing y(c)=!y(c).

Together with the existing disjointness of every active translated slice from
Q_v, this shows that all one-coordinate active translates of one completion
cube form pairwise disjoint layers.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem translatedCompletionWords_disjoint_same_owner_distinct_active
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V} {c d : Fin n}
    (hc : c ∈ retainedActive C v)
    (hcd : c ≠ d) :
    Disjoint
      (translatedCompletionWords C v c)
      (translatedCompletionWords C v d) := by
  classical
  rw [Finset.disjoint_left]
  intro word hcWord hdWord
  have hcSrc :
      flipBoolWordAt word c ∈ retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v c word).1 hcWord
  have hdSrc :
      flipBoolWordAt word d ∈ retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v d word).1 hdWord
  have hcComp :=
    (mem_retainedCompletionWords C v
      (flipBoolWordAt word c)).1 hcSrc
  have hdComp :=
    (mem_retainedCompletionWords C v
      (flipBoolWordAt word d)).1 hdSrc
  have hcAt := hcComp c hc
  have hdAt := hdComp c hc
  have hdc : c ≠ d := hcd
  rw [flipBoolWordAt_at] at hcAt
  rw [flipBoolWordAt_off word hdc] at hdAt
  have hcontra : Bool.not (word c) = word c :=
    hcAt.trans hdAt.symm
  cases h : word c <;> simp [h] at hcontra

theorem translatedCompletionWords_pairwise_disjoint_on_active
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) :
    Set.Pairwise
      (retainedActive C v : Set (Fin n))
      (fun c d =>
        Disjoint
          (translatedCompletionWords C v c)
          (translatedCompletionWords C v d)) := by
  intro c hc d hd hcd
  exact translatedCompletionWords_disjoint_same_owner_distinct_active
    C hc hcd

#print axioms translatedCompletionWords_disjoint_same_owner_distinct_active
#print axioms translatedCompletionWords_pairwise_disjoint_on_active

end OrderedEdgeColoring
end JSP000404Research
