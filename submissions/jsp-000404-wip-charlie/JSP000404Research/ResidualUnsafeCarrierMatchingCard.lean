import JSP000404Research.ResidualUnsafeOverlapMatching
import Mathlib.Tactic

/-!
# Cardinality bound for unsafe residual overlap carriers

ResidualUnsafeOverlapMatching proves that unsafe residual carrier edges with
a common retained completion word form a matching: two such ordered edges
sharing any endpoint are equal.

This file converts that structural statement into the numerical bound

  2 * number_of_unsafe_carriers <= number_of_vertices.

For a six-vertex terminal there are therefore at most three unsafe carriers.
-/

namespace JSP000404Research

/-- Generic finite matching-cardinality lemma for ordered pairs. -/
theorem matching_orderedPairs_two_mul_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V × V))
    (hne :
      ∀ e ∈ E, e.1 ≠ e.2)
    (hmatch :
      ∀ e ∈ E, ∀ f ∈ E,
        (e.1 = f.1 ∨ e.1 = f.2 ∨
         e.2 = f.1 ∨ e.2 = f.2) →
        e = f) :
    2 * E.card ≤ Fintype.card V := by
  let endpoint :
      ({e // e ∈ E} × Bool) → V :=
    fun eb =>
      if eb.2 then eb.1.1.2 else eb.1.1.1
  have hinj : Function.Injective endpoint := by
    intro x y hxy
    rcases x with ⟨⟨e, he⟩, bx⟩
    rcases y with ⟨⟨f, hf⟩, by⟩
    cases bx <;> cases by
    · simp only [endpoint, Bool.false_eq_true, if_false] at hxy
      have hef : e = f :=
        hmatch e he f hf (Or.inl hxy)
      subst f
      rfl
    · simp only [endpoint, Bool.false_eq_true, if_false, if_true] at hxy
      have hef : e = f :=
        hmatch e he f hf (Or.inr (Or.inl hxy))
      subst f
      have hbad : e.1 = e.2 := hxy
      exact False.elim ((hne e he) hbad)
    · simp only [endpoint, Bool.false_eq_true, if_false, if_true] at hxy
      have hef : e = f :=
        hmatch e he f hf (Or.inr (Or.inr (Or.inl hxy)))
      subst f
      have hbad : e.2 = e.1 := hxy
      exact False.elim ((hne e he) hbad.symm)
    · simp only [endpoint, if_true] at hxy
      have hef : e = f :=
        hmatch e he f hf (Or.inr (Or.inr (Or.inr hxy)))
      subst f
      rfl
  have hcard :=
    Fintype.card_le_of_injective endpoint hinj
  simpa [Fintype.card_prod, Fintype.card_coe] using hcard

namespace OrderedEdgeColoring

/-- Unsafe residual carrier pairs which actually carry a common retained
completion word. -/
noncomputable def unsafeOverlapCarrierPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Finset (V × V) := by
  classical
  exact Finset.univ.filter fun e =>
    e.1 < e.2 ∧
    (¬ ∃ c : Fin n, c ∉ residualForbidden C e.1 e.2) ∧
    ∃ word : Fin n → Bool,
      word ∈ retainedCompletionWords C e.1 ∧
      word ∈ retainedCompletionWords C e.2

@[simp] theorem mem_unsafeOverlapCarrierPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) :
    (u,v) ∈ unsafeOverlapCarrierPairs C ↔
      u < v ∧
      (¬ ∃ c : Fin n, c ∉ residualForbidden C u v) ∧
      ∃ word : Fin n → Bool,
        word ∈ retainedCompletionWords C u ∧
        word ∈ retainedCompletionWords C v := by
  classical
  simp [unsafeOverlapCarrierPairs]

/-- Unsafe overlap carriers are a genuine matching, hence use two distinct
vertices per carrier. -/
theorem unsafeOverlapCarrierPairs_two_mul_card_le
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    2 * (unsafeOverlapCarrierPairs C).card ≤
      Fintype.card V := by
  classical
  apply matching_orderedPairs_two_mul_card_le
      (unsafeOverlapCarrierPairs C)
  · intro e he
    have hdata :=
      (mem_unsafeOverlapCarrierPairs C e.1 e.2).1 he
    exact ne_of_lt hdata.1
  · intro e he f hf hshare
    have heData :=
      (mem_unsafeOverlapCarrierPairs C e.1 e.2).1 he
    have hfData :=
      (mem_unsafeOverlapCarrierPairs C f.1 f.2).1 hf
    obtain ⟨wordE, heU, heV⟩ := heData.2.2
    obtain ⟨wordF, hfU, hfV⟩ := hfData.2.2
    have hpairs :=
      unsafe_overlap_edges_matching
        C heData.1 hfData.1
        heData.2.1 hfData.2.1
        heU heV hfU hfV hshare
    exact Prod.ext hpairs.1 hpairs.2

/-- Six-vertex specialization. -/
theorem unsafeOverlapCarrierPairs_card_le_three_of_card_six
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (hcard : Fintype.card V = 6) :
    (unsafeOverlapCarrierPairs C).card ≤ 3 := by
  have h :=
    unsafeOverlapCarrierPairs_two_mul_card_le C
  rw [hcard] at h
  omega

#print axioms matching_orderedPairs_two_mul_card_le
#print axioms unsafeOverlapCarrierPairs_two_mul_card_le
#print axioms unsafeOverlapCarrierPairs_card_le_three_of_card_six

end OrderedEdgeColoring
end JSP000404Research
