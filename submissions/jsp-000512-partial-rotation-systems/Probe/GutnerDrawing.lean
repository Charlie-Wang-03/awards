import Probe.GutnerCoordinates
import Probe.GutnerObstruction

namespace JSP512Probe.Gutner
open StraightLine

/-- Every graph edge is one of the listed local edges, in either direction. -/
theorem adj_edge (a b : Fin 86) (h : graph.Adj a b) :
    ∃ i k, (a = (edge i k).1 ∧ b = (edge i k).2) ∨
      (a = (edge i k).2 ∧ b = (edge i k).1) := by
  obtain ⟨_,i,r,s,hrs,hab⟩ := h
  obtain ⟨k,hk⟩ := edgeTable_complete r s hrs
  refine ⟨i,k,?_⟩
  simpa only [edge,hk] using hab

/-- The explicit 86-vertex obstruction has a noncrossing straight-line drawing
in the real plane. Finite sign certificates are checked by the Lean kernel. -/
def drawing : StraightLine.Drawing graph :=
  drawingOfChecks graph position position_injective (by
    intro a b v hab hva hvb
    obtain ⟨i,k,h⟩ := adj_edge a b hab
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact vertex_checks i k v hva hvb
    · rw [orient_reverse]
      exact neg_ne_zero.mpr (vertex_checks i k v hvb hva)) (by
    intro a b c d hab hcd h1 h2
    obtain ⟨i,k,ha⟩ := adj_edge a b hab
    obtain ⟨j,l,hb⟩ := adj_edge c d hcd
    rcases ha with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      rcases hb with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals
      have hn : edge i k ≠ edge j l := by
        intro h
        have hf := congrArg Prod.fst h
        have ht := congrArg Prod.snd h
        tauto
      have hr : edge i k ≠ ((edge j l).2,(edge j l).1) := by
        intro h
        have hf := congrArg Prod.fst h
        have ht := congrArg Prod.snd h
        simp only at hf ht
        tauto
      have hp := pair_checks i k j l hn hr
      first
      | exact hp
      | exact separated_reverse_left _ _ _ _ hp
      | exact separated_reverse_right _ _ _ _ hp
      | exact separated_reverse_left _ _ _ _ (separated_reverse_right _ _ _ _ hp))

/-- Geometric sharpness witness: four-element lists on an explicitly drawn
finite graph need not have a proper list coloring. -/
theorem geometric_four_list_obstruction :
    Nonempty (StraightLine.Drawing graph) ∧
    (∀ v, (lists v).card = 4) ∧
    ¬ ∃ c : graph.Coloring ℕ, ListColoring.Respects graph lists c :=
  ⟨⟨drawing⟩,lists_card,no_list_coloring⟩

end JSP512Probe.Gutner
