import JSP000404Research.ResidualSafeSupportMatching
import JSP000404Research.ResidualUnsafeCarrierMatchingCard
import Mathlib.Tactic

/-!
# Global matching of support-unsafe overlap carriers

Package the no-active-safe overlap carriers into a finite edge set.  These are
exactly the overlap residual pairs for which every safe retained coordinate is
inactive at both endpoints.

The endpoint-canonical-word argument proves that these pairs form a genuine
matching.  Hence two vertices are consumed per carrier and

  2 * card(supportUnsafeOverlapCarrierPairs) <= card V.

This is the global combinatorial interface for the final safe/common-inactive
hard subtype.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def supportUnsafeOverlapCarrierPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Finset (V × V) := by
  classical
  exact Finset.univ.filter fun e =>
    e.1 < e.2 ∧
    NoActiveSafeCoordinate C e.1 e.2 ∧
    ∃ word : Fin n → Bool,
      word ∈ retainedCompletionWords C e.1 ∧
      word ∈ retainedCompletionWords C e.2

@[simp] theorem mem_supportUnsafeOverlapCarrierPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) :
    (u,v) ∈ supportUnsafeOverlapCarrierPairs C ↔
      u < v ∧
      NoActiveSafeCoordinate C u v ∧
      ∃ word : Fin n → Bool,
        word ∈ retainedCompletionWords C u ∧
        word ∈ retainedCompletionWords C v := by
  classical
  simp [supportUnsafeOverlapCarrierPairs]

theorem supportUnsafeOverlapCarrierPairs_matching
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {e f : V × V}
    (he : e ∈ supportUnsafeOverlapCarrierPairs C)
    (hf : f ∈ supportUnsafeOverlapCarrierPairs C)
    (hshare :
      e.1 = f.1 ∨ e.1 = f.2 ∨
      e.2 = f.1 ∨ e.2 = f.2) :
    e = f := by
  have heData :=
    (mem_supportUnsafeOverlapCarrierPairs C e.1 e.2).1 he
  have hfData :=
    (mem_supportUnsafeOverlapCarrierPairs C f.1 f.2).1 hf
  obtain ⟨wordE, heU, heV⟩ := heData.2.2
  obtain ⟨wordF, hfU, hfV⟩ := hfData.2.2
  have hpairs :=
    noActiveSafe_overlap_edges_matching
      C heData.1 hfData.1
      heData.2.1 hfData.2.1
      heU heV hfU hfV hshare
  exact Prod.ext hpairs.1 hpairs.2

theorem supportUnsafeOverlapCarrierPairs_two_mul_card_le
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    2 * (supportUnsafeOverlapCarrierPairs C).card ≤
      Fintype.card V := by
  classical
  apply matching_orderedPairs_two_mul_card_le
    (supportUnsafeOverlapCarrierPairs C)
  · intro e he
    have hdata :=
      (mem_supportUnsafeOverlapCarrierPairs C e.1 e.2).1 he
    exact ne_of_lt hdata.1
  · intro e he f hf hshare
    exact supportUnsafeOverlapCarrierPairs_matching
      C he hf hshare

theorem supportUnsafeOverlapCarrierPairs_endpoint_unique
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {e f : V × V}
    (he : e ∈ supportUnsafeOverlapCarrierPairs C)
    (hf : f ∈ supportUnsafeOverlapCarrierPairs C)
    (hef : e ≠ f) :
    e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧
    e.2 ≠ f.1 ∧ e.2 ≠ f.2 := by
  constructor
  · intro h
    exact hef
      (supportUnsafeOverlapCarrierPairs_matching
        C he hf (Or.inl h))
  constructor
  · intro h
    exact hef
      (supportUnsafeOverlapCarrierPairs_matching
        C he hf (Or.inr (Or.inl h)))
  constructor
  · intro h
    exact hef
      (supportUnsafeOverlapCarrierPairs_matching
        C he hf (Or.inr (Or.inr (Or.inl h))))
  · intro h
    exact hef
      (supportUnsafeOverlapCarrierPairs_matching
        C he hf (Or.inr (Or.inr (Or.inr h))))

#print axioms supportUnsafeOverlapCarrierPairs_matching
#print axioms supportUnsafeOverlapCarrierPairs_two_mul_card_le
#print axioms supportUnsafeOverlapCarrierPairs_endpoint_unique

end OrderedEdgeColoring
end JSP000404Research
