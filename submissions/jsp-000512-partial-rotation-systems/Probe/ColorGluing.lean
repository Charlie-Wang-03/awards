import Probe.ListColorExtension

namespace JSP512Probe.ListColoring
variable {V C : Type*} (G : SimpleGraph V)

/-- Colorings of two induced pieces glue when every edge lies in one piece and
the colorings agree on the overlap. Both local colorings are preserved. -/
theorem glue_induced (A B : Set V)
    (cover : ∀ x, x ∈ A ∨ x ∈ B)
    (edges : ∀ x y, G.Adj x y → (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B))
    (cA : (G.induce A).Coloring C) (cB : (G.induce B).Coloring C)
    (agree : ∀ x (ha : x ∈ A) (hb : x ∈ B), cA ⟨x,ha⟩ = cB ⟨x,hb⟩) :
    ∃ c : G.Coloring C, (∀ x : A, c x.val = cA x) ∧ (∀ x : B, c x.val = cB x) := by
  classical
  let f : V → C := fun x => if h : x ∈ A then cA ⟨x,h⟩ else cB ⟨x,(cover x).resolve_left h⟩
  have left : ∀ x : A, f x.val = cA x := by
    intro x
    simp only [f, dite_eq_left x.property]
  have right : ∀ x : B, f x.val = cB x := by
    intro x
    by_cases h : x.val ∈ A
    · simp only [f, dite_eq_left h]
      exact agree x.val h x.property
    · simp only [f, dite_eq_right h]
  have valid : ∀ {x y}, G.Adj x y → f x ≠ f y := by
    intro x y h
    rcases edges x y h with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · rw [left ⟨x,hx⟩,left ⟨y,hy⟩]
      exact cA.valid (show (G.induce A).Adj ⟨x,hx⟩ ⟨y,hy⟩ from h)
    · rw [right ⟨x,hx⟩,right ⟨y,hy⟩]
      exact cB.valid (show (G.induce B).Adj ⟨x,hx⟩ ⟨y,hy⟩ from h)
  exact ⟨SimpleGraph.Coloring.mk f valid,left,right⟩

/-- Respecting original lists is preserved when induced-piece colorings glue. -/
theorem glue_induced_lists (A B : Set V) (L : V → Finset C)
    (cover : ∀ x, x ∈ A ∨ x ∈ B)
    (edges : ∀ x y, G.Adj x y → (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B))
    (cA : (G.induce A).Coloring C) (cB : (G.induce B).Coloring C)
    (agree : ∀ x (ha : x ∈ A) (hb : x ∈ B), cA ⟨x,ha⟩ = cB ⟨x,hb⟩)
    (hA : Respects (G.induce A) (fun x => L x.val) cA)
    (hB : Respects (G.induce B) (fun x => L x.val) cB) :
    ∃ c : G.Coloring C, Respects G L c ∧
      (∀ x : A, c x.val = cA x) ∧ (∀ x : B, c x.val = cB x) := by
  obtain ⟨c,ha,hb⟩ := glue_induced G A B cover edges cA cB agree
  refine ⟨c,?_,ha,hb⟩
  intro x
  rcases cover x with hx | hx
  · rw [ha ⟨x,hx⟩]; exact hA ⟨x,hx⟩
  · rw [hb ⟨x,hx⟩]; exact hB ⟨x,hx⟩

variable [DecidableEq V]

/-- Precolor the common chord endpoints after coloring the first piece. -/
def chordLists (L : V → Finset C) (s t : V) (a b : C) : V → Finset C :=
  fun x => if x = s then {a} else if x = t then {b} else L x

/-- Coloring the second piece with singleton lists on the separating chord
forces agreement; gluing preserves the entire first coloring. The separator
and edge-cover hypotheses are explicit and must be proved geometrically. -/
theorem glue_along_chord (A B : Set V) (L : V → Finset C) (s t : V)
    (hsA : s ∈ A) (htA : t ∈ A) (hchord : G.Adj s t)
    (cover : ∀ x, x ∈ A ∨ x ∈ B)
    (edges : ∀ x y, G.Adj x y → (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B))
    (overlap : ∀ x, x ∈ A → x ∈ B → x = s ∨ x = t)
    (cA : (G.induce A).Coloring C)
    (hA : Respects (G.induce A) (fun x => L x.val) cA)
    (cB : (G.induce B).Coloring C)
    (hB : Respects (G.induce B)
      (fun x => chordLists L s t (cA ⟨s,hsA⟩) (cA ⟨t,htA⟩) x.val) cB) :
    ∃ c : G.Coloring C, Respects G L c ∧
      (∀ x : A, c x.val = cA x) ∧ (∀ x : B, c x.val = cB x) := by
  have agree : ∀ x (ha : x ∈ A) (hb : x ∈ B), cA ⟨x,ha⟩ = cB ⟨x,hb⟩ := by
    intro x ha hb
    have hm := hB ⟨x,hb⟩
    change cB ⟨x,hb⟩ ∈ chordLists L s t (cA ⟨s,hsA⟩) (cA ⟨t,htA⟩) x at hm
    rcases overlap x ha hb with rfl | rfl
    · simp [chordLists] at hm
      exact hm.symm
    · simp [chordLists,hchord.ne.symm] at hm
      exact hm.symm
  have lists : Respects (G.induce B) (fun x => L x.val) cB := by
    intro x
    change cB x ∈ L x.val
    by_cases hs : x.val = s
    · have he : cB x = cA ⟨s,hsA⟩ := by
        have hm := hB x
        simpa [chordLists,hs] using hm
      rw [he,hs]
      exact hA ⟨s,hsA⟩
    · by_cases ht : x.val = t
      · have he : cB x = cA ⟨t,htA⟩ := by
          have hm := hB x
          simpa [chordLists,ht,hchord.ne.symm] using hm
        rw [he,ht]
        exact hA ⟨t,htA⟩
      · have hm := hB x
        simpa only [chordLists,ite_eq_right hs,ite_eq_right ht] using hm
  exact glue_induced_lists G A B L cover edges cA cB agree hA lists
omit [DecidableEq V] in
/-- The chord endpoints inherit distinct colors from the first proper coloring. -/
theorem chord_endpoint_colors_ne (A : Set V) (s t : V) (hs : s ∈ A) (ht : t ∈ A)
    (hadj : G.Adj s t) (c : (G.induce A).Coloring C) : c ⟨s,hs⟩ ≠ c ⟨t,ht⟩ :=
  c.valid (show (G.induce A).Adj ⟨s,hs⟩ ⟨t,ht⟩ from hadj)

/-- Precoloring a chord changes exactly its endpoint lists. -/
theorem chordLists_unchanged (L : V → Finset C) (s t x : V) (a b : C)
    (hs : x ≠ s) (ht : x ≠ t) : chordLists L s t a b x = L x := by
  simp only [chordLists,ite_eq_right hs,ite_eq_right ht]

/-- List size invariants on the second side of a chord. The old boundary must
remain on the new boundary, and old protected vertices in this side must be
chord endpoints. These are explicit obligations of the disk decomposition. -/
theorem chord_list_bounds (L : V → Finset C) (oldBoundary P side newBoundary : Set V)
    (s t : V) (a b : C)
    (old_on_new : ∀ x ∈ side, x ∈ oldBoundary → x ∈ newBoundary)
    (hprotected : ∀ x ∈ side, x ∈ P → x = s ∨ x = t)
    (hboundary : ∀ x ∈ oldBoundary, x ∉ P → 3 ≤ (L x).card)
    (hinterior : ∀ x ∉ oldBoundary, x ∉ P → 5 ≤ (L x).card)
    (x : V) (hx : x ∈ side) (hs : x ≠ s) (ht : x ≠ t) :
    (x ∈ newBoundary → 3 ≤ (chordLists L s t a b x).card) ∧
    (x ∉ newBoundary → 5 ≤ (chordLists L s t a b x).card) := by
  rw [chordLists_unchanged L s t x a b hs ht]
  have hp : x ∉ P := fun h => (hprotected x hx h).elim hs ht
  constructor
  · intro _
    by_cases ho : x ∈ oldBoundary
    · exact hboundary x ho hp
    · have hh := hinterior x ho hp
      omega
  · intro hn
    exact hinterior x (fun ho => hn (old_on_new x hx ho)) hp

end JSP512Probe.ListColoring
