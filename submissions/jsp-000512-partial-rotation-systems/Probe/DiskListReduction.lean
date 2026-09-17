import Probe.DiskInstance
import Probe.ListColorExtension

namespace JSP512Probe.RotationSystem
open ListColoring
variable {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

/-- The chordless reduction uses the actual new disk and its actual outer face.
Its reduced list bounds and protected lists are verified, and any respecting
coloring of that smaller instance extends without changing surviving colors. -/
theorem disk_list_reduction_region (outer : G.Dart) (hD : R.IsTriangulatedDisk outer)
    (hcorner : R.face outer ≠ outer.symm)
    (hchord : ∀ a, R.face.SameCycle outer a → G.Adj outer.snd a.fst →
      a.fst = outer.fst ∨ a.fst = (R.face outer).snd)
    (L : V → Finset C) (P : Set V) (hPB : P ⊆ R.facialVertices outer)
    (hboundary : ∀ x ∈ R.facialVertices outer, x ∉ P → 3 ≤ (L x).card)
    (hinterior : ∀ x ∉ R.facialVertices outer, x ∉ P → 5 ≤ (L x).card)
    (k : C) (hsingle : L outer.fst = {k}) (hLv : 3 ≤ (L outer.snd).card) :
    ∃ a ∈ L outer.snd, ∃ b ∈ L outer.snd, a ≠ b ∧ a ≠ k ∧ b ≠ k ∧
      ∃ root : (VertexDeletedGraph (G := G) outer.snd).Dart,
        (R.deleteVertex outer.snd).IsTriangulatedDisk root ∧
        (∀ x, (R.deleteVertex outer.snd).face.SameCycle root x ↔ R.outerDeletionRegion outer x) ∧
        (∀ x : {x : V | x ≠ outer.snd}, x.val ∉ P →
          (x ∈ (R.deleteVertex outer.snd).facialVertices root →
            3 ≤ (reducedLists G L outer.snd outer.fst (R.face outer).snd a b x).card) ∧
          (x ∉ (R.deleteVertex outer.snd).facialVertices root →
            5 ≤ (reducedLists G L outer.snd outer.fst (R.face outer).snd a b x).card)) ∧
        (∀ x : {x : V | x ≠ outer.snd}, x.val ∈ P →
          reducedLists G L outer.snd outer.fst (R.face outer).snd a b x = L x.val) ∧
        (∀ c : (DeletedVertex G outer.snd).Coloring C,
          Respects (DeletedVertex G outer.snd)
            (reducedLists G L outer.snd outer.fst (R.face outer).snd a b) c →
          ∃ c' : G.Coloring C, Respects G L c' ∧
            (∀ x : {x : V // x ≠ outer.snd}, c' x.val = c x) ∧
            (c' outer.snd = a ∨ c' outer.snd = b)) := by
  have chord : ∀ x ∈ R.facialVertices outer, G.Adj outer.snd x →
      x = outer.fst ∨ x = (R.face outer).snd := by
    rintro x ⟨d,hd,rfl⟩ ha
    exact hchord d hd ha
  have ht : (R.face outer).snd ≠ outer.snd := by
    have h := (R.face outer).snd_ne_fst
    rwa [R.face_source] at h
  obtain ⟨a,ha,b,hb,hab,hak,hbk,hext⟩ := three_list_reduction G L outer.snd outer.fst
    (R.face outer).snd outer.adj.ne ht k hsingle hLv
  obtain ⟨root,hroot,hregion,hvertices⟩ := R.disk_delete_instance outer hD hcorner hchord
  refine ⟨a,ha,b,hb,hab,hak,hbk,root,hroot,hregion,?_,?_,hext⟩
  · intro x hx
    have hh := reduced_list_bounds G L (R.facialVertices outer) P outer.snd outer.fst
      (R.face outer).snd a b chord hboundary hinterior x hx
    have he : x ∈ (R.deleteVertex outer.snd).facialVertices root ↔
        x ∈ enlargedBoundary G (R.facialVertices outer) outer.snd := hvertices x
    exact ⟨fun h => hh.1 (he.mp h), fun h => hh.2 (fun h' => h (he.mpr h'))⟩
  · intro x hx
    exact protected_lists_unchanged G L (R.facialVertices outer) P outer.snd outer.fst
      (R.face outer).snd a b hPB chord x hx
/-- Compatibility projection omitting the explicit deleted-face orbit. -/
theorem disk_list_reduction (outer : G.Dart) (hD : R.IsTriangulatedDisk outer)
    (hcorner : R.face outer ≠ outer.symm)
    (hchord : ∀ a, R.face.SameCycle outer a → G.Adj outer.snd a.fst →
      a.fst = outer.fst ∨ a.fst = (R.face outer).snd)
    (L : V → Finset C) (P : Set V) (hPB : P ⊆ R.facialVertices outer)
    (hboundary : ∀ x ∈ R.facialVertices outer, x ∉ P → 3 ≤ (L x).card)
    (hinterior : ∀ x ∉ R.facialVertices outer, x ∉ P → 5 ≤ (L x).card)
    (k : C) (hsingle : L outer.fst = {k}) (hLv : 3 ≤ (L outer.snd).card) :
    ∃ a ∈ L outer.snd, ∃ b ∈ L outer.snd, a ≠ b ∧ a ≠ k ∧ b ≠ k ∧
      ∃ root : (VertexDeletedGraph (G := G) outer.snd).Dart,
        (R.deleteVertex outer.snd).IsTriangulatedDisk root ∧
        (∀ x : {x : V | x ≠ outer.snd}, x.val ∉ P →
          (x ∈ (R.deleteVertex outer.snd).facialVertices root →
            3 ≤ (reducedLists G L outer.snd outer.fst (R.face outer).snd a b x).card) ∧
          (x ∉ (R.deleteVertex outer.snd).facialVertices root →
            5 ≤ (reducedLists G L outer.snd outer.fst (R.face outer).snd a b x).card)) ∧
        (∀ x : {x : V | x ≠ outer.snd}, x.val ∈ P →
          reducedLists G L outer.snd outer.fst (R.face outer).snd a b x = L x.val) ∧
        (∀ c : (DeletedVertex G outer.snd).Coloring C,
          Respects (DeletedVertex G outer.snd)
            (reducedLists G L outer.snd outer.fst (R.face outer).snd a b) c →
          ∃ c' : G.Coloring C, Respects G L c' ∧
            (∀ x : {x : V // x ≠ outer.snd}, c' x.val = c x) ∧
            (c' outer.snd = a ∨ c' outer.snd = b)) := by
  obtain ⟨a,ha,b,hb,hab,hak,hbk,root,hroot,_,hbounds,hprotected,hext⟩ :=
    R.disk_list_reduction_region outer hD hcorner hchord L P hPB hboundary hinterior k hsingle hLv
  exact ⟨a,ha,b,hb,hab,hak,hbk,root,hroot,hbounds,hprotected,hext⟩

end JSP512Probe.RotationSystem
