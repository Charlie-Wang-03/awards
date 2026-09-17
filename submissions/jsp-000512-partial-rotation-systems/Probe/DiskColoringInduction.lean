import Probe.PrecoloredDeletion

namespace JSP512Probe.RotationSystem
open ListColoring

/-- Every finite triangulated genus-zero disk extends a proper precoloring of
one outer edge when the other outer lists have size at least three and the
interior lists have size at least five. The induction is on actual vertex count. -/
theorem triangulated_disk_precolored {V C : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G) (pre : G.Dart)
    (hD : R.IsTriangulatedDisk pre) : PrecoloredDiskColorable R pre C := by
  classical
  by_cases hback : R.face pre = pre.symm
  · intro L a b hLa hLb hab _
    obtain ⟨c,hc,_,_⟩ := R.disk_backtracking_coloring pre hD hback L a b
      (by simp [hLa]) (by simp [hLb]) hab
    exact ⟨c,hc⟩
  · have solve : ∀ A : Set V, Nat.card A < Fintype.card V →
        ∀ [Fintype A] (U : RotationSystem (G.induce A)) c, U.IsTriangulatedDisk c →
          PrecoloredDiskColorable U c C := by
      intro A hA _ U c hU
      exact triangulated_disk_precolored (V := A) (G := G.induce A) U c hU
    let outer := R.face pre
    have ht : pre.snd = outer.fst := (R.face_source pre).symm
    have hs : pre.fst ≠ outer.snd := by
      intro he
      apply hback
      exact SimpleGraph.Dart.ext _ _ (Prod.ext ht.symm he.symm)
    have ho : R.face.SameCycle pre outer := Equiv.Perm.SameCycle.rfl.apply_right
    have hO := hD.reroot R ho
    have hcorner : R.face outer ≠ outer.symm := by
      intro hb
      rcases R.disk_backtracking_vertices outer hO hb pre.fst with hh | hh
      · exact pre.adj.ne (hh.trans ht.symm)
      · exact hs hh
    by_cases hchord : ∀ d, R.face.SameCycle outer d → G.Adj outer.snd d.fst →
        d.fst = outer.fst ∨ d.fst = (R.face outer).snd
    · exact R.precolored_delete_step outer pre hO hcorner ho.symm ht hs hchord solve
    · push Not at hchord
      obtain ⟨d,hd,hadj,hleft,hright⟩ := hchord
      obtain ⟨D⟩ := R.chord_sector_data outer hO hcorner d hd hadj hleft hright
      exact ChordSectorData.precolored_step R outer pre hO d.fst D ho.symm ht hs solve
termination_by Fintype.card V
decreasing_by simpa only [Nat.card_eq_fintype_card] using hA

end JSP512Probe.RotationSystem
