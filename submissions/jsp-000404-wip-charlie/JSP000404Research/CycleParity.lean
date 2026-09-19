import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Tactic

/-!
# Cycle parity outlet

Mathlib already proves that an odd cycle graph of size at least three has
chromatic number three.  Therefore any Boolean vertex colouring of a cycle
graph forces even length.

This small lemma is the graph-theoretic outlet needed by the wrap-band parity
argument: the geometric work only has to manufacture a Boolean colouring of
the abstract cycle indices.
-/

namespace JSP000404Research

open SimpleGraph

theorem even_of_cycleGraph_bool_coloring
    {m : ℕ} (hm : 3 ≤ m)
    (c : (cycleGraph m).Coloring Bool) :
    Even m := by
  by_contra hnot
  have hodd : Odd m := Nat.not_even_iff_odd.mp hnot
  have hchrom := chromaticNumber_cycleGraph_of_odd m (by omega) hodd
  have htwo : (cycleGraph m).Colorable 2 := by
    simpa using c.colorable
  have hle := htwo.chromaticNumber_le
  rw [hchrom] at hle
  norm_num at hle

/-- Equivalent formulation using bipartiteness. -/
theorem even_of_cycleGraph_isBipartite
    {m : ℕ} (hm : 3 ≤ m)
    (h : (cycleGraph m).IsBipartite) :
    Even m := by
  obtain ⟨c⟩ := h
  exact even_of_cycleGraph_bool_coloring hm
    (SimpleGraph.recolorOfEquiv (cycleGraph m) finTwoEquiv.symm c)


/-- Abstract cyclic switch rule.

Think of `high i` as the L/H type of cycle edge `i`, and `up i` as
whether that edge points upward in the ambient linear order.  If along every
adjacency of the abstract cycle, the L/H type stays the same exactly when the
order direction flips, then the Boolean label
`decide (high i = up i)` alternates on every cycle edge. -/
theorem even_of_cycle_switch_rule
    {m : ℕ} (hm : 3 ≤ m)
    (high up : Fin m → Bool)
    (hswitch : ∀ {i j},
      (cycleGraph m).Adj i j →
        (high i = high j ↔ up i ≠ up j)) :
    Even m := by
  let c : (cycleGraph m).Coloring Bool :=
    SimpleGraph.Coloring.mk
      (fun i => decide (high i = up i)) (by
        intro i j hij
        have hs := hswitch hij
        cases hi : high i <;>
          cases hj : high j <;>
          cases ui : up i <;>
          cases uj : up j <;>
          simp_all)
  exact even_of_cycleGraph_bool_coloring hm c

#print axioms even_of_cycle_switch_rule

#print axioms even_of_cycleGraph_bool_coloring
#print axioms even_of_cycleGraph_isBipartite

end JSP000404Research
