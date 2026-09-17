import Probe.PrecoloredDisk
import Probe.DiskListReduction

namespace JSP512Probe.RotationSystem
open ListColoring
variable {V C : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In the chordless case the actual surviving precolored edge roots the
smaller disk, and a respecting coloring extends over the deleted vertex. -/
theorem precolored_delete_step (R : RotationSystem G) (outer pre : G.Dart)
    (hD : R.IsTriangulatedDisk outer) (hcorner : R.face outer ≠ outer.symm)
    (hpre : R.face.SameCycle outer pre) (ht : pre.snd = outer.fst)
    (hs : pre.fst ≠ outer.snd)
    (hchord : ∀ d, R.face.SameCycle outer d → G.Adj outer.snd d.fst →
      d.fst = outer.fst ∨ d.fst = (R.face outer).snd)
    (solve : ∀ A : Set V, Nat.card A < Fintype.card V →
      ∀ [Fintype A] (U : RotationSystem (G.induce A)) c, U.IsTriangulatedDisk c →
        PrecoloredDiskColorable U c C) :
    PrecoloredDiskColorable R pre C := by
  classical
  intro L a b hLa hLb hab hbound
  have htne : pre.snd ≠ outer.snd := ht ▸ outer.adj.ne
  have hbdy := R.facialVertices_reroot hpre
  have hPB : ({pre.fst,pre.snd} : Set V) ⊆ R.facialVertices outer := by
    intro u hu
    rcases hu with rfl | rfl
    · exact ⟨pre,hpre,rfl⟩
    · exact ⟨R.face pre,hpre.apply_right,R.face_source pre⟩
  have hLv : 3 ≤ (L outer.snd).card :=
    (hbound outer.snd hs.symm htne.symm).1
      (hbdy ▸ (show outer.snd ∈ R.facialVertices outer from
        ⟨R.face outer,Equiv.Perm.SameCycle.rfl.apply_right,R.face_source outer⟩))
  obtain ⟨d,_,f,_,_,_,_,root,hroot,hregion,hbounds,hprotected,hext⟩ :=
    R.disk_list_reduction_region outer hD hcorner hchord L {pre.fst,pre.snd} hPB
      (fun x hx hp => (hbound x (fun h => hp (Or.inl h)) (fun h => hp (Or.inr h))).1
        (hbdy ▸ hx))
      (fun x hx hp => (hbound x (fun h => hp (Or.inl h)) (fun h => hp (Or.inr h))).2
        (fun hh => hx (hbdy.symm ▸ hh))) b (ht ▸ hLb) hLv
  let A : Set V := {x | x ≠ outer.snd}
  have hA : Nat.card A < Fintype.card V := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_lt (p := fun x => x ∈ A) (x := outer.snd) (by simp [A])
  let e := (vertexDeletedDartEquiv outer.snd).symm ⟨pre,hs,htne⟩
  have he := R.deleted_outer_edge outer root hregion pre hpre hs htne
  have hrootE := hroot.reroot (R.deleteVertex outer.snd) he
  have hboundary := (R.deleteVertex outer.snd).facialVertices_reroot he
  let LR := reducedLists G L outer.snd outer.fst (R.face outer).snd d f
  obtain ⟨c,hc⟩ := solve A hA (R.deleteVertex outer.snd) e hrootE LR a b
    ((hprotected e.fst (Or.inl rfl)).trans hLa)
    ((hprotected e.snd (Or.inr rfl)).trans hLb) hab (by
      intro x hxs hxt
      have hp : x.val ∉ ({pre.fst,pre.snd} : Set V) := by
        rintro (hh | hh)
        · exact hxs (Subtype.ext hh)
        · exact hxt (Subtype.ext hh)
      simpa only [hboundary] using hbounds x hp)
  obtain ⟨c',hc',_,_⟩ := hext c hc
  exact ⟨c',hc'⟩

end JSP512Probe.RotationSystem
