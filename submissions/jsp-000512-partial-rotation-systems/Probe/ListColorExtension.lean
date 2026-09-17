import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Card

namespace JSP512Probe.ListColoring
variable {V C : Type*} (G : SimpleGraph V) [DecidableEq V] [DecidableEq C]
  [DecidableRel G.Adj]

/-- A proper Mathlib coloring that chooses each vertex's color from its list. -/
def Respects (L : V → Finset C) (c : G.Coloring C) : Prop := ∀ v, c v ∈ L v

abbrev DeletedVertex (v : V) := G.induce {x | x ≠ v}

/-- Reserve two colors at neighbors of the removed vertex, except the protected
precolored vertex and one boundary neighbor whose color is dealt with last. -/
def reducedLists (L : V → Finset C) (v s t : V) (a b : C) : {x : V // x ≠ v} → Finset C :=
  fun x => if G.Adj v x.val ∧ x.val ≠ s ∧ x.val ≠ t then L x.val \ {a,b} else L x.val

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- A list of at least three colors offers two distinct choices avoiding a fixed color. -/
theorem reserve_two (L : Finset C) (k : C) (hL : 3 ≤ L.card) :
    ∃ a ∈ L, ∃ b ∈ L, a ≠ b ∧ a ≠ k ∧ b ≠ k := by
  have hcard : 1 < (L.erase k).card := by
    by_cases hk : k ∈ L
    · rw [Finset.card_erase_of_mem hk]
      omega
    · rw [Finset.erase_eq_of_notMem hk]
      omega
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hcard
  exact ⟨a,(Finset.mem_erase.mp ha).2,b,(Finset.mem_erase.mp hb).2,hab,
    (Finset.mem_erase.mp ha).1,(Finset.mem_erase.mp hb).1⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Removing the two reserved colors from an interior list leaves at least three. -/
theorem five_to_three (L : Finset C) (a b : C) (hL : 5 ≤ L.card) :
    3 ≤ (L \ {a,b}).card := by
  have h := Finset.card_le_card_sdiff_add_card (s := L) (t := {a,b})
  have hp : ({a,b} : Finset C).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
  omega

/-- Extend a coloring of the vertex-deleted graph by choosing between the two
reserved colors after the exceptional boundary neighbor has been colored.
The existing coloring is preserved at every surviving vertex. -/
theorem extend_two_choices (L : V → Finset C) (v s t : V)
    (hs : s ≠ v) (ht : t ≠ v) (a b k : C)
    (ha : a ∈ L v) (hb : b ∈ L v) (hab : a ≠ b) (hak : a ≠ k) (hbk : b ≠ k)
    (c : (DeletedVertex G v).Coloring C)
    (hc : Respects (DeletedVertex G v) (reducedLists G L v s t a b) c)
    (hcs : c ⟨s,hs⟩ = k) :
    ∃ c' : G.Coloring C, Respects G L c' ∧
      (∀ x : {x : V // x ≠ v}, c' x.val = c x) ∧ (c' v = a ∨ c' v = b) := by
  classical
  let chosen := if a = c ⟨t,ht⟩ then b else a
  have hchoice : chosen = a ∨ chosen = b := by
    dsimp [chosen]
    split_ifs <;> simp
  have htcolor : chosen ≠ c ⟨t,ht⟩ := by
    dsimp [chosen]
    split_ifs with h
    · exact fun h' => hab (h.trans h'.symm)
    · exact h
  have hkcolor : chosen ≠ k := hchoice.elim (fun h => h ▸ hak) (fun h => h ▸ hbk)
  have hneighbor : ∀ x : {x : V // x ≠ v}, G.Adj v x.val → chosen ≠ c x := by
    intro x hx
    by_cases hxs : x.val = s
    · have he : x = ⟨s,hs⟩ := Subtype.ext hxs
      rw [he,hcs]
      exact hkcolor
    · by_cases hxt : x.val = t
      · have he : x = ⟨t,ht⟩ := Subtype.ext hxt
        rw [he]
        exact htcolor
      · have hm := hc x
        change c x ∈ reducedLists G L v s t a b x at hm
        have hcond : G.Adj v x.val ∧ x.val ≠ s ∧ x.val ≠ t := ⟨hx,hxs,hxt⟩
        simp only [reducedLists, ite_eq_left hcond, Finset.mem_sdiff, Finset.mem_insert,
          Finset.mem_singleton] at hm
        intro h
        exact hm.2 (hchoice.elim (fun h' => Or.inl (h.symm.trans h'))
          (fun h' => Or.inr (h.symm.trans h')))
  let color : V → C := fun x => if h : x = v then chosen else c ⟨x,h⟩
  have hold : ∀ x : {x : V // x ≠ v}, color x.val = c x := by
    intro x
    simp only [color, dite_eq_right x.property]
    exact congrArg c (Subtype.ext rfl)
  have hnew : color v = chosen := by simp only [color, dite_eq_left rfl]
  have valid : ∀ {x y}, G.Adj x y → color x ≠ color y := by
    intro x y hxy
    by_cases hx : x = v
    · subst x
      have hy : y ≠ v := hxy.ne.symm
      rw [hnew, hold ⟨y,hy⟩]
      exact hneighbor ⟨y,hy⟩ hxy
    · by_cases hy : y = v
      · subst y
        rw [hold ⟨x,hx⟩, hnew]
        exact (hneighbor ⟨x,hx⟩ hxy.symm).symm
      · rw [hold ⟨x,hx⟩, hold ⟨y,hy⟩]
        exact c.valid (show (DeletedVertex G v).Adj ⟨x,hx⟩ ⟨y,hy⟩ from hxy)
  refine ⟨SimpleGraph.Coloring.mk color valid, ?_, hold, ?_⟩
  · intro x
    change color x ∈ L x
    by_cases hx : x = v
    · subst x
      rw [hnew]
      exact hchoice.elim (fun h => h ▸ ha) (fun h => h ▸ hb)
    · rw [hold ⟨x,hx⟩]
      have hm := hc ⟨x,hx⟩
      change c ⟨x,hx⟩ ∈ reducedLists G L v s t a b ⟨x,hx⟩ at hm
      unfold reducedLists at hm
      split_ifs at hm
      · exact (Finset.mem_sdiff.mp hm).1
      · exact hm
  · change color v = a ∨ color v = b
    rw [hnew]
    exact hchoice

/-- The candidate new boundary after removing a boundary vertex: old boundary
vertices together with its neighbors. Geometric validity must be proved separately. -/
def enlargedBoundary (B : Set V) (v : V) : Set {x : V // x ≠ v} :=
  {x | x.val ∈ B ∨ G.Adj v x.val}

/-- If the removed vertex has only its two boundary neighbors on the old
boundary, no old boundary list is reduced. -/
theorem old_boundary_list_unchanged (L : V → Finset C) (B : Set V) (v s t : V)
    (a b : C) (hchord : ∀ x ∈ B, G.Adj v x → x = s ∨ x = t)
    (x : {x : V // x ≠ v}) (hx : x.val ∈ B) :
    reducedLists G L v s t a b x = L x.val := by
  unfold reducedLists
  apply ite_eq_right
  rintro ⟨ha,hs,ht⟩
  exact (hchord x.val hx ha).elim hs ht

/-- The 3-on-boundary / 5-in-interior list sizes are preserved by the reduction,
for every vertex outside an explicitly protected precolored set. -/
theorem reduced_list_bounds (L : V → Finset C) (B P : Set V) (v s t : V) (a b : C)
    (hchord : ∀ x ∈ B, G.Adj v x → x = s ∨ x = t)
    (hboundary : ∀ x ∈ B, x ∉ P → 3 ≤ (L x).card)
    (hinterior : ∀ x ∉ B, x ∉ P → 5 ≤ (L x).card)
    (x : {x : V // x ≠ v}) (hxP : x.val ∉ P) :
    (x ∈ enlargedBoundary G B v → 3 ≤ (reducedLists G L v s t a b x).card) ∧
    (x ∉ enlargedBoundary G B v → 5 ≤ (reducedLists G L v s t a b x).card) := by
  constructor
  · intro hx
    rcases hx with hx | hx
    · rw [old_boundary_list_unchanged G L B v s t a b hchord x hx]
      exact hboundary x.val hx hxP
    · by_cases hB : x.val ∈ B
      · rw [old_boundary_list_unchanged G L B v s t a b hchord x hB]
        exact hboundary x.val hB hxP
      · have hsize := hinterior x.val hB hxP
        unfold reducedLists
        split_ifs
        · exact five_to_three (L x.val) a b hsize
        · omega
  · intro hx
    have hB : x.val ∉ B := fun h => hx (Or.inl h)
    have hAdj : ¬G.Adj v x.val := fun h => hx (Or.inr h)
    have hcond : ¬(G.Adj v x.val ∧ x.val ≠ s ∧ x.val ≠ t) := fun h => hAdj h.1
    simp only [reducedLists, ite_eq_right hcond]
    exact hinterior x.val hB hxP

/-- Every protected old-boundary list, including singleton precolor lists,
is preserved exactly by the two-color reduction. -/
theorem protected_lists_unchanged (L : V → Finset C) (B P : Set V) (v s t : V) (a b : C)
    (hPB : P ⊆ B) (hchord : ∀ x ∈ B, G.Adj v x → x = s ∨ x = t)
    (x : {x : V // x ≠ v}) (hx : x.val ∈ P) :
    reducedLists G L v s t a b x = L x.val :=
  old_boundary_list_unchanged G L B v s t a b hchord x (hPB hx)

/-- The complete algebraic boundary reduction: choose two colors from a
three-element list, protect a singleton-colored neighbor, and extend any
coloring of the reduced instance without changing surviving colors. -/
theorem three_list_reduction (L : V → Finset C) (v s t : V)
    (hs : s ≠ v) (ht : t ≠ v) (k : C) (hsingle : L s = {k}) (hLv : 3 ≤ (L v).card) :
    ∃ a ∈ L v, ∃ b ∈ L v, a ≠ b ∧ a ≠ k ∧ b ≠ k ∧
      ∀ c : (DeletedVertex G v).Coloring C,
        Respects (DeletedVertex G v) (reducedLists G L v s t a b) c →
        ∃ c' : G.Coloring C, Respects G L c' ∧
          (∀ x : {x : V // x ≠ v}, c' x.val = c x) ∧ (c' v = a ∨ c' v = b) := by
  obtain ⟨a,ha,b,hb,hab,hak,hbk⟩ := reserve_two (L v) k hLv
  refine ⟨a,ha,b,hb,hab,hak,hbk,?_⟩
  intro c hc
  have hcs : c ⟨s,hs⟩ = k := by
    have hm := hc ⟨s,hs⟩
    change c ⟨s,hs⟩ ∈ reducedLists G L v s t a b ⟨s,hs⟩ at hm
    simpa only [reducedLists, ne_eq, not_true_eq_false, false_and, and_false,
      ite_false, hsingle, Finset.mem_singleton] using hm
  exact extend_two_choices G L v s t hs ht a b k ha hb hab hak hbk c hc hcs

end JSP512Probe.ListColoring
