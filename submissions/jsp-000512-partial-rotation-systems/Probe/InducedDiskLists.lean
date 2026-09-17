import Probe.ColorGluing
import Probe.DiskInstance

namespace JSP512Probe.RotationSystem
open ListColoring
variable {V C : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Boundary inheritance supplies both list lower bounds on an actual induced
disk. New boundary vertices may keep their larger original interior lists. -/
theorem induced_disk_list_bounds (outer : G.Dart) (A : Set V)
    [Fintype A] (S : RotationSystem (G.induce A)) (root : (G.induce A).Dart)
    (hboundary : ∀ u : A, u.val ∈ R.facialVertices outer → u ∈ S.facialVertices root)
    (L : V → Finset C) (P : Set V)
    (hthree : ∀ u ∈ R.facialVertices outer, u ∉ P → 3 ≤ (L u).card)
    (hfive : ∀ u ∉ R.facialVertices outer, u ∉ P → 5 ≤ (L u).card) :
    ∀ u : A, u.val ∉ P →
      (u ∈ S.facialVertices root → 3 ≤ (L u.val).card) ∧
      (u ∉ S.facialVertices root → 5 ≤ (L u.val).card) := by
  intro u hp
  constructor
  · intro _
    by_cases hb : u.val ∈ R.facialVertices outer
    · exact hthree u.val hb hp
    · have h := hfive u.val hb hp
      omega
  · intro hn
    exact hfive u.val (fun ho => hn (hboundary u ho)) hp

omit [Fintype V] [DecidableRel G.Adj] in
/-- Precoloring the separating chord preserves the required three/five list
bounds on every other vertex of the actual second disk. -/
theorem induced_chord_list_bounds (outer : G.Dart) (A : Set V)
    [Fintype A] (S : RotationSystem (G.induce A)) (root : (G.induce A).Dart)
    (hboundary : ∀ u : A, u.val ∈ R.facialVertices outer → u ∈ S.facialVertices root)
    (L : V → Finset C) (P : Set V) (s t : V) (a b : C)
    (hprotected : ∀ u : A, u.val ∈ P → u.val = s ∨ u.val = t)
    (hthree : ∀ u ∈ R.facialVertices outer, u ∉ P → 3 ≤ (L u).card)
    (hfive : ∀ u ∉ R.facialVertices outer, u ∉ P → 5 ≤ (L u).card) :
    ∀ u : A, u.val ≠ s → u.val ≠ t →
      (u ∈ S.facialVertices root → 3 ≤ (chordLists L s t a b u.val).card) ∧
      (u ∉ S.facialVertices root → 5 ≤ (chordLists L s t a b u.val).card) := by
  intro u hs ht
  rw [chordLists_unchanged L s t u.val a b hs ht]
  exact R.induced_disk_list_bounds outer A S root hboundary L P hthree hfive u
    (fun hp => (hprotected u hp).elim hs ht)

end JSP512Probe.RotationSystem

namespace JSP512Probe.ListColoring
variable {V : Type*} (G : SimpleGraph V)

/-- An edge incident to a vertex exclusive to the first side lies wholly in
that side. Any protected endpoint also in the second side must be on the chord. -/
theorem protected_edge_side (A B : Set V) (s t p q : V)
    (hedges : ∀ u v, G.Adj u v → (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B))
    (hinter : ∀ u, (u ∈ A ∧ u ∈ B) ↔ u = s ∨ u = t)
    (hp : p ∉ B) (hpq : G.Adj p q) :
    p ∈ A ∧ q ∈ A ∧ ∀ u ∈ B, u = p ∨ u = q → u = s ∨ u = t := by
  have he : p ∈ A ∧ q ∈ A := (hedges p q hpq).resolve_right (fun h => hp h.1)
  refine ⟨he.1,he.2,?_⟩
  intro u hu h
  rcases h with rfl | rfl
  · exact False.elim (hp hu)
  · exact (hinter _).mp ⟨he.2,hu⟩

end JSP512Probe.ListColoring
