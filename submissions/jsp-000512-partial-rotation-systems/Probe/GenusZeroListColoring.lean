import Probe.DiskColoringInduction
import Probe.TriangularFaces

namespace JSP512Probe.RotationSystem
open ListColoring
variable {V C : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The precolored-edge theorem implies the usual three/five disk list theorem. -/
theorem triangulated_disk_list_coloring (R : RotationSystem G) (pre : G.Dart)
    (hD : R.IsTriangulatedDisk pre) (L : V → Finset C)
    (hb : ∀ x ∈ R.facialVertices pre, 3 ≤ (L x).card)
    (hi : ∀ x ∉ R.facialVertices pre, 5 ≤ (L x).card) :
    ∃ c : G.Coloring C, Respects G L c := by
  classical
  have hs := hb pre.fst ⟨pre,Equiv.Perm.SameCycle.rfl,rfl⟩
  have ht := hb pre.snd ⟨R.face pre,Equiv.Perm.SameCycle.rfl.apply_right,R.face_source pre⟩
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (by omega : 0 < (L pre.fst).card)
  obtain ⟨b,hb',_,_,_,hba,_⟩ := reserve_two (L pre.snd) a ht
  let LP := chordLists L pre.fst pre.snd a b
  obtain ⟨c,hc⟩ := R.triangulated_disk_precolored pre hD LP a b
    (by simp [LP,chordLists]) (by simp [LP,chordLists,pre.adj.ne.symm]) hba.symm (by
      intro x hxs hxt
      simp only [LP,chordLists_unchanged L pre.fst pre.snd x a b hxs hxt]
      exact ⟨hb x,hi x⟩)
  refine ⟨c,?_⟩
  intro x
  have hh := hc x
  by_cases hxs : x = pre.fst
  · have he : c x = a := by simpa [LP,chordLists,hxs] using hh
    rw [he,hxs]
    exact ha
  · by_cases hxt : x = pre.snd
    · have he : c x = b := by simpa [LP,chordLists,hxt,pre.adj.ne.symm] using hh
      rw [he,hxt]
      exact hb'
    · simpa only [LP,chordLists_unchanged L pre.fst pre.snd x a b hxs hxt] using hh

/-- A graph of at most two vertices needs only two-element lists. -/
theorem small_graph_list_coloring (hn : Fintype.card V ≤ 2) (L : V → Finset C)
    (hL : ∀ x, 2 ≤ (L x).card) : ∃ c : G.Coloring C, Respects G L c := by
  classical
  by_cases hedge : ∃ s t, G.Adj s t
  · obtain ⟨s,t,hst⟩ := hedge
    have cover : ∀ x, x = s ∨ x = t := by
      intro x
      by_contra hh
      push Not at hh
      have hc : ({s,t,x} : Finset V).card = 3 := by
        simp [hst.ne,hh.1.symm,hh.2.symm]
      have hle := Finset.card_le_univ ({s,t,x} : Finset V)
      omega
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (by have := hL s; omega : 0 < (L s).card)
    have he : 0 < ((L t).erase a).card := by
      by_cases hm : a ∈ L t
      · rw [Finset.card_erase_of_mem hm]; have := hL t; omega
      · rw [Finset.erase_eq_of_notMem hm]; have := hL t; omega
    obtain ⟨b,hb⟩ := Finset.card_pos.mp he
    have hba := (Finset.mem_erase.mp hb).1
    let f : V → C := fun x => if x = s then a else b
    have valid : ∀ {x y}, G.Adj x y → f x ≠ f y := by
      intro x y hxy
      rcases cover x with rfl | rfl <;> rcases cover y with rfl | rfl
      · exact False.elim (G.irrefl hxy)
      · simpa [f,hst.ne.symm] using hba.symm
      · simpa [f,hst.ne.symm] using hba
      · exact False.elim (G.irrefl hxy)
    refine ⟨SimpleGraph.Coloring.mk f valid,?_⟩
    intro x
    change f x ∈ L x
    rcases cover x with rfl | rfl
    · simpa [f] using ha
    · simpa [f,hst.ne.symm] using (Finset.mem_erase.mp hb).2
  · have nonempty : ∀ x, (L x).Nonempty := fun x => Finset.card_pos.mp (by have := hL x; omega)
    let f : V → C := fun x => Classical.choose (nonempty x)
    refine ⟨SimpleGraph.Coloring.mk f (fun {x y} h => False.elim (hedge ⟨x,y,h⟩)),?_⟩
    exact fun x => Classical.choose_spec (nonempty x)

/-- Every finite graph with a genus-zero rotation system is five-list-colorable.
Maximal augmentation and the disk coloring induction are both constructed. -/
theorem genusZero_five_list_coloring (R : RotationSystem G) (hz : R.HasGenusZero)
    (L : V → Finset C) (hL : ∀ x, 5 ≤ (L x).card) :
    ∃ c : G.Coloring C, Respects G L c := by
  classical
  by_cases hn : 3 ≤ Fintype.card V
  · obtain ⟨H,hGH,S,hS,hmax⟩ := exists_maximal_augmentation G R hz
    let : DecidableRel H.Adj := Classical.decRel _
    have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    have hconn := S.maximal_connected hS hmax
    by_cases hedge : ∃ s t, H.Adj s t
    · obtain ⟨s,t,hst⟩ := hedge
      let pre : H.Dart := ⟨(s,t),hst⟩
      have hD : S.IsTriangulatedDisk pre :=
        ⟨hS,hconn,fun a b ha hb he => S.maximal_face_vertex_injective a b hS hmax (ha.symm.trans hb) he,
          fun d _ => S.maximal_face_three_steps hS hmax hn d⟩
      obtain ⟨c,hc⟩ := S.triangulated_disk_list_coloring pre hD L
        (fun x _ => by have := hL x; omega) (fun x _ => hL x)
      exact ⟨SimpleGraph.Coloring.mk (fun x => c x) (fun h => c.valid (hGH h)),hc⟩
    · have nonempty : ∀ x, (L x).Nonempty := fun x => Finset.card_pos.mp (by have := hL x; omega)
      let f : V → C := fun x => Classical.choose (nonempty x)
      refine ⟨SimpleGraph.Coloring.mk f (fun {x y} h => False.elim (hedge ⟨x,y,hGH h⟩)),?_⟩
      exact fun x => Classical.choose_spec (nonempty x)
  · exact small_graph_list_coloring (by omega) L (fun x => by have := hL x; omega)

end JSP512Probe.RotationSystem
