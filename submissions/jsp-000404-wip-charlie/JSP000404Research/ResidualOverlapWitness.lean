
import JSP000404Research.ResidualCompletionAccounting
import Mathlib.Tactic

/-!
# Every projected overlap word is carried by one residual edge

An overlap completion word has fibre cardinality exactly two.  Therefore it
determines a unique unordered pair of vertices.  Ordering that pair by the
ambient linear order produces a unique residual edge u<v whose two retained
completion cubes both contain the word.

This is the bridge from the exact overlap count in
ResidualCompletionAccounting back to the residual-edge geometry.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem exists_ordered_residual_pair_of_overlapWord
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {word : Fin n → Bool}
    (hoverlap : word ∈ overlapCompletionWords C) :
    ∃ u v : V,
      u < v ∧
      IsResidual C u v ∧
      word ∈ retainedCompletionWords C u ∧
      word ∈ retainedCompletionWords C v ∧
      ∀ x : V,
        word ∈ retainedCompletionWords C x →
        x = u ∨ x = v := by
  classical
  have hcard :
      (completionFibre C word).card = 2 :=
    (mem_overlapCompletionWords C word).1 hoverlap
  obtain ⟨a, b, hab, hfibre⟩ :=
    Finset.card_eq_two.mp hcard
  have haF : a ∈ completionFibre C word := by
    rw [hfibre]
    simp
  have hbF : b ∈ completionFibre C word := by
    rw [hfibre]
    simp
  have ha :
      word ∈ retainedCompletionWords C a :=
    (mem_completionFibre C word a).1 haF
  have hb :
      word ∈ retainedCompletionWords C b :=
    (mem_completionFibre C word b).1 hbF
  have huniq :
      ∀ x : V,
        word ∈ retainedCompletionWords C x →
        x = a ∨ x = b := by
    intro x hx
    have hxF :
        x ∈ completionFibre C word :=
      (mem_completionFibre C word x).2 hx
    rw [hfibre] at hxF
    simpa [eq_comm] using hxF
  rcases lt_or_gt_of_ne hab with hablt | hbalt
  · have hres :=
      isResidual_of_retainedCompletion_overlap_lt
        C hablt ha hb
    exact ⟨a, b, hablt, hres, ha, hb, huniq⟩
  · have hres :=
      isResidual_of_retainedCompletion_overlap_lt
        C hbalt hb ha
    refine ⟨b, a, hbalt, hres, hb, ha, ?_⟩
    intro x hx
    rcases huniq x hx with hxa | hxb
    · exact Or.inr hxa
    · exact Or.inl hxb

/-- Two ordered residual pairs carrying the same overlap word are equal. -/
theorem ordered_residual_pair_unique_of_overlapWord
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {word : Fin n → Bool}
    (hoverlap : word ∈ overlapCompletionWords C)
    {u v u' v' : V}
    (huv : u < v)
    (huv' : u' < v')
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v)
    (hu' : word ∈ retainedCompletionWords C u')
    (hv' : word ∈ retainedCompletionWords C v') :
    u = u' ∧ v = v' := by
  obtain ⟨a, b, hab, _hres, ha, hb, huniq⟩ :=
    exists_ordered_residual_pair_of_overlapWord C hoverlap
  have huAB := huniq u hu
  have hvAB := huniq v hv
  have hu'AB := huniq u' hu'
  have hv'AB := huniq v' hv'
  have huvAB : u = a ∧ v = b := by
    rcases huAB with hua | hub
    · have hvb : v = b := by
        rcases hvAB with hva | hvb
        · subst u
          subst v
          exact False.elim ((lt_irrefl a) huv)
        · exact hvb
      exact ⟨hua, hvb⟩
    · have hva : v = a := by
        rcases hvAB with hva | hvb
        · exact hva
        · subst u
          subst v
          exact False.elim ((lt_irrefl b) huv)
      subst u
      subst v
      exact False.elim ((not_lt_of_ge hab.le) huv)
  have huvAB' : u' = a ∧ v' = b := by
    rcases hu'AB with hua | hub
    · have hvb : v' = b := by
        rcases hv'AB with hva | hvb
        · subst u'
          subst v'
          exact False.elim ((lt_irrefl a) huv')
        · exact hvb
      exact ⟨hua, hvb⟩
    · have hva : v' = a := by
        rcases hv'AB with hva | hvb
        · exact hva
        · subst u'
          subst v'
          exact False.elim ((lt_irrefl b) huv')
      subst u'
      subst v'
      exact False.elim ((not_lt_of_ge hab.le) huv')
  exact ⟨huvAB.1.trans huvAB'.1.symm,
    huvAB.2.trans huvAB'.2.symm⟩

/-- Exact projected-loss vertices never participate in projected overlap
words. -/
theorem overlapWord_not_mem_exact_projected_loss_completion
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {r : ℕ} {v : V} {word : Fin n → Bool}
    (hv :
      v ∈ layerLossSet exponent (projectedFree C) r)
    (hoverlap :
      word ∈ overlapCompletionWords C) :
    word ∉ retainedCompletionWords C v := by
  intro hvWord
  obtain ⟨u, w, huw, _hres, huWord, hwWord, huniq⟩ :=
    exists_ordered_residual_pair_of_overlapWord C hoverlap
  have hvEq := huniq v hvWord
  rcases hvEq with rfl | rfl
  · have hdisj :=
      exact_projected_loss_completion_disjoint
        C exponent hexp honeLoss hv (ne_of_lt huw)
    exact Finset.disjoint_left.mp hdisj
      hvWord hwWord
  · have hdisj :=
      exact_projected_loss_completion_disjoint
        C exponent hexp honeLoss hv (ne_of_lt huw).symm
    exact Finset.disjoint_left.mp hdisj
      hvWord huWord

#print axioms exists_ordered_residual_pair_of_overlapWord
#print axioms ordered_residual_pair_unique_of_overlapWord
#print axioms overlapWord_not_mem_exact_projected_loss_completion

end OrderedEdgeColoring
end JSP000404Research
