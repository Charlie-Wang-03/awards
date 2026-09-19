import JSP000404Research.OrderedEdgeColor
import Mathlib.Tactic

/-!
# Eliminating one residual ordered-edge colour

Start with an admissible ordered colouring by k+1 colours.  Regard the final
colour as residual.  Retain every old colour whose value is < k and reassign
each residual edge to a target colour in Fin k.

The only new monochromatic two-paths that can appear are those touching at
least one residual edge.  A local safety hypothesis on exactly those paths is
therefore sufficient to obtain a new OrderedEdgeColoring by k colours.

A stronger optional absorption hypothesis says that every residual edge is
sent to a colour which was already incident, through retained edges, at both
of its endpoints.  Then recolouring creates no new active colour at any
vertex.  This is the combinatorial interface intended for Erdős--Szekeres
style adaptive direction recolouring.
-/

namespace JSP000404Research

open scoped BigOperators

namespace OrderedEdgeColoring

/-- Projection of a non-residual old colour to Fin k. -/
def retainedColor
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1))
    (u v : V)
    (h : (C.color u v).val < k) : Fin k :=
  ⟨(C.color u v).val, h⟩

/-- Recolour all residual edges, i.e. old edges whose colour has value k. -/
noncomputable def recoloredColor
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1))
    (target : V → V → Fin k) :
    V → V → Fin k :=
  fun u v =>
    if h : (C.color u v).val < k then
      retainedColor C u v h
    else
      target u v

/-- The retained old colours incident to a vertex, projected to Fin k. -/
noncomputable def retainedActive
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1))
    (v : V) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun c =>
    (∃ a, a < v ∧ C.color a v = c.castSucc) ∨
    (∃ w, v < w ∧ C.color v w = c.castSucc)

/-- Data sufficient to eliminate the residual colour. -/
structure ResidualRecoloring
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1)) where
  target : V → V → Fin k
  safe_touching_residual :
    ∀ {a v w : V}, a < v → v < w →
      (¬(C.color a v).val < k ∨ ¬(C.color v w).val < k) →
      recoloredColor C target a v ≠ recoloredColor C target v w

namespace ResidualRecoloring

/-- If both consecutive edges retain old colours, admissibility is inherited
from the original colouring. -/
theorem retained_pair_ne
    {V : Type*} [LinearOrder V] {k : ℕ}
    {C : OrderedEdgeColoring V (k + 1)}
    (R : ResidualRecoloring C)
    {a v w : V} (hav : a < v) (hvw : v < w)
    (havRet : (C.color a v).val < k)
    (hvwRet : (C.color v w).val < k) :
    recoloredColor C R.target a v ≠
      recoloredColor C R.target v w := by
  simp only [recoloredColor, dif_pos havRet, dif_pos hvwRet]
  intro heq
  apply C.noMonoTwoPath hav hvw
  apply Fin.ext
  exact congrArg Fin.val heq

/-- Eliminate the residual colour and obtain an admissible k-colouring. -/
noncomputable def toOrderedEdgeColoring
    {V : Type*} [LinearOrder V] {k : ℕ}
    {C : OrderedEdgeColoring V (k + 1)}
    (R : ResidualRecoloring C) :
    OrderedEdgeColoring V k where
  color := recoloredColor C R.target
  noMonoTwoPath := by
    intro a v w hav hvw
    by_cases havRet : (C.color a v).val < k
    · by_cases hvwRet : (C.color v w).val < k
      · exact R.retained_pair_ne hav hvw havRet hvwRet
      · exact R.safe_touching_residual hav hvw (Or.inr hvwRet)
    · exact R.safe_touching_residual hav hvw (Or.inl havRet)

/-- Target colours used by residual edges incident to a vertex. -/
noncomputable def residualTargets
    {V : Type*} [LinearOrder V] {k : ℕ}
    {C : OrderedEdgeColoring V (k + 1)}
    (R : ResidualRecoloring C)
    (v : V) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun c =>
    (∃ a, a < v ∧ ¬(C.color a v).val < k ∧ R.target a v = c) ∨
    (∃ w, v < w ∧ ¬(C.color v w).val < k ∧ R.target v w = c)

/-- Every active colour after recolouring is either a retained old colour or
a target colour used by an incident residual edge. -/
theorem active_subset_retained_union_targets
    {V : Type*} [LinearOrder V] {k : ℕ}
    {C : OrderedEdgeColoring V (k + 1)}
    (R : ResidualRecoloring C)
    (v : V) :
    active R.toOrderedEdgeColoring v ⊆
      retainedActive C v ∪ R.residualTargets v := by
  classical
  intro c hc
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at hc
  rcases hc with ⟨a, hav, hcol⟩ | ⟨w, hvw, hcol⟩
  · by_cases hret : (C.color a v).val < k
    · apply Finset.mem_union_left
      simp only [retainedActive, Finset.mem_filter, Finset.mem_univ, true_and]
      apply Or.inl
      refine ⟨a, hav, ?_⟩
      apply Fin.ext
      have hval := congrArg Fin.val hcol
      simpa [toOrderedEdgeColoring, recoloredColor, hret, retainedColor] using hval
    · apply Finset.mem_union_right
      simp only [residualTargets, Finset.mem_filter, Finset.mem_univ, true_and]
      apply Or.inl
      refine ⟨a, hav, hret, ?_⟩
      simpa [toOrderedEdgeColoring, recoloredColor, hret] using hcol
  · by_cases hret : (C.color v w).val < k
    · apply Finset.mem_union_left
      simp only [retainedActive, Finset.mem_filter, Finset.mem_univ, true_and]
      apply Or.inr
      refine ⟨w, hvw, ?_⟩
      apply Fin.ext
      have hval := congrArg Fin.val hcol
      simpa [toOrderedEdgeColoring, recoloredColor, hret, retainedColor] using hval
    · apply Finset.mem_union_right
      simp only [residualTargets, Finset.mem_filter, Finset.mem_univ, true_and]
      apply Or.inr
      refine ⟨w, hvw, hret, ?_⟩
      simpa [toOrderedEdgeColoring, recoloredColor, hret] using hcol

/-- Pointwise retained-plus-target colour budgets control the final active
colour count. -/
theorem active_card_le_of_union_budget
    {V : Type*} [LinearOrder V] {k : ℕ}
    {C : OrderedEdgeColoring V (k + 1)}
    (R : ResidualRecoloring C)
    (ell : V → ℕ)
    (hbudget : ∀ v,
      (retainedActive C v ∪ R.residualTargets v).card ≤ ell v) :
    ∀ v, (active R.toOrderedEdgeColoring v).card ≤ ell v := by
  intro v
  exact (Finset.card_le_card
    (R.active_subset_retained_union_targets v)).trans (hbudget v)

/-- Direct Kraft outlet under the exact pointwise recolouring budget. -/
theorem cluster_capacity_of_recoloring_budget
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    {C : OrderedEdgeColoring V (k + 1)}
    (R : ResidualRecoloring C)
    (exponent ell : V → ℕ)
    (hexponent : ∀ v, exponent v ≤ k)
    (hell : ∀ v, ell v = k - exponent v)
    (hbudget : ∀ v,
      (retainedActive C v ∪ R.residualTargets v).card ≤ ell v) :
    ∑ v, 2 ^ exponent v ≤ 2 ^ k := by
  apply cluster_capacity_of_active_le
    R.toOrderedEdgeColoring exponent ell hexponent hell
  exact R.active_card_le_of_union_budget ell hbudget

/-- Optional absorption condition: a residual edge is reassigned to a colour
already represented by retained old edges at both endpoints. -/
def IsAbsorbed
    {V : Type*} [LinearOrder V] {k : ℕ}
    {C : OrderedEdgeColoring V (k + 1)}
    (R : ResidualRecoloring C) : Prop :=
  ∀ {u v : V}, u < v → ¬(C.color u v).val < k →
    R.target u v ∈ retainedActive C u ∧
    R.target u v ∈ retainedActive C v

/-- Under absorption, every active colour after recolouring was already a
retained active colour at that vertex. -/
theorem active_subset_retainedActive
    {V : Type*} [LinearOrder V] {k : ℕ}
    {C : OrderedEdgeColoring V (k + 1)}
    (R : ResidualRecoloring C)
    (habs : R.IsAbsorbed)
    (v : V) :
    active R.toOrderedEdgeColoring v ⊆ retainedActive C v := by
  classical
  intro c hc
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at hc
  rcases hc with ⟨a, hav, hcol⟩ | ⟨w, hvw, hcol⟩
  · by_cases hret : (C.color a v).val < k
    · have hold :
          C.color a v = c.castSucc := by
        apply Fin.ext
        have hval := congrArg Fin.val hcol
        simpa [toOrderedEdgeColoring, recoloredColor, hret, retainedColor] using hval
      simp only [retainedActive, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inl ⟨a, hav, hold⟩
    · have ht :
          R.target a v = c := by
        simpa [toOrderedEdgeColoring, recoloredColor, hret] using hcol
      have ha := (habs hav hret).2
      simpa [ht] using ha
  · by_cases hret : (C.color v w).val < k
    · have hold :
          C.color v w = c.castSucc := by
        apply Fin.ext
        have hval := congrArg Fin.val hcol
        simpa [toOrderedEdgeColoring, recoloredColor, hret, retainedColor] using hval
      simp only [retainedActive, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inr ⟨w, hvw, hold⟩
    · have ht :
          R.target v w = c := by
        simpa [toOrderedEdgeColoring, recoloredColor, hret] using hcol
      have ha := (habs hvw hret).1
      simpa [ht] using ha

/-- Hence absorbed recolouring cannot increase the retained active-colour
count at any vertex. -/
theorem active_card_le_retainedActive
    {V : Type*} [LinearOrder V] {k : ℕ}
    {C : OrderedEdgeColoring V (k + 1)}
    (R : ResidualRecoloring C)
    (habs : R.IsAbsorbed)
    (v : V) :
    (active R.toOrderedEdgeColoring v).card ≤
      (retainedActive C v).card :=
  Finset.card_le_card (R.active_subset_retainedActive habs v)

/-- Direct Kraft outlet for an absorbed residual recolouring. -/
theorem cluster_capacity_of_absorbed_recoloring
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    {C : OrderedEdgeColoring V (k + 1)}
    (R : ResidualRecoloring C)
    (habs : R.IsAbsorbed)
    (exponent ell : V → ℕ)
    (hexponent : ∀ v, exponent v ≤ k)
    (hell : ∀ v, ell v = k - exponent v)
    (hretained : ∀ v, (retainedActive C v).card ≤ ell v) :
    ∑ v, 2 ^ exponent v ≤ 2 ^ k := by
  apply cluster_capacity_of_active_le
    R.toOrderedEdgeColoring exponent ell hexponent hell
  intro v
  exact (R.active_card_le_retainedActive habs v).trans (hretained v)

#print axioms retained_pair_ne
#print axioms toOrderedEdgeColoring
#print axioms active_subset_retained_union_targets
#print axioms active_card_le_of_union_budget
#print axioms cluster_capacity_of_recoloring_budget
#print axioms active_subset_retainedActive
#print axioms active_card_le_retainedActive
#print axioms cluster_capacity_of_absorbed_recoloring

end ResidualRecoloring
end OrderedEdgeColoring
end JSP000404Research
