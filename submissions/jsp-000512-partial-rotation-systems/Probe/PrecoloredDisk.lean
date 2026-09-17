import Probe.DiskBaseCase
import Probe.ChordProtectedVertices

namespace JSP512Probe.RotationSystem
open ListColoring
variable {V C : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The strengthened disk coloring statement used by vertex-count induction. -/
def PrecoloredDiskColorable (R : RotationSystem G) (pre : G.Dart) (C : Type*) : Prop :=
  ∀ (L : V → Finset C) (a b : C), L pre.fst = {a} → L pre.snd = {b} → a ≠ b →
    (∀ x, x ≠ pre.fst → x ≠ pre.snd →
      (x ∈ R.facialVertices pre → 3 ≤ (L x).card) ∧
      (x ∉ R.facialVertices pre → 5 ≤ (L x).card)) →
    ∃ c : G.Coloring C, Respects G L c

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Moving the root around the same face leaves its boundary vertex set fixed. -/
theorem facialVertices_reroot (R : RotationSystem G) {a b : G.Dart}
    (h : R.face.SameCycle a b) : R.facialVertices a = R.facialVertices b := by
  ext u
  constructor
  · rintro ⟨d,hd,hu⟩
    exact ⟨d,h.symm.trans hd,hu⟩
  · rintro ⟨d,hd,hu⟩
    exact ⟨d,h.trans hd,hu⟩

/-- The chord case calls the strengthened coloring theorem on the two actual
smaller induced disks and glues their list colorings. -/
theorem ChordSectorData.precolored_step (R : RotationSystem G) (outer pre : G.Dart)
    (hD : R.IsTriangulatedDisk outer) (w : V) (D : R.ChordSectorData outer w)
    (hpre : R.face.SameCycle outer pre) (ht : pre.snd = outer.fst)
    (hs : pre.fst ≠ outer.snd)
    (solve : ∀ A : Set V, Nat.card A < Fintype.card V →
      ∀ [Fintype A] (U : RotationSystem (G.induce A)) c, U.IsTriangulatedDisk c →
        PrecoloredDiskColorable U c C) :
    PrecoloredDiskColorable R pre C := by
  classical
  intro L a b hLa hLb hab hbound
  let A := restoreSide outer.snd D.boundarySide
  let B := restoreSide outer.snd D.exposedSide
  let : Fintype A := Fintype.ofFinite _
  let : Fintype B := Fintype.ofFinite _
  obtain ⟨hcov,hedges,hinter,hA,hB⟩ := D.separator
  obtain ⟨U,c,hU,hcs,hct,hboundary,hincoming⟩ := D.boundary_disk_boundary_edges hD.simple hD.inner
  obtain ⟨e,he,hes,het⟩ := hincoming pre hpre ht hs
  have hUe := hU.reroot U he
  have hprebound := R.facialVertices_reroot hpre
  have hce := U.facialVertices_reroot he
  have hboundsA := R.induced_disk_list_bounds outer A U c hboundary L
    {pre.fst,pre.snd}
    (fun x hx hp => (hbound x (fun h => hp (Or.inl h)) (fun h => hp (Or.inr h))).1
      (hprebound ▸ hx))
    (fun x hx hp => (hbound x (fun h => hp (Or.inl h)) (fun h => hp (Or.inr h))).2
      (fun hh => hx (hprebound.symm ▸ hh)))
  obtain ⟨cA,hcA⟩ := solve A hA U e hUe (fun x => L x.val) a b
    (by simpa only [hes] using hLa) (by simpa only [het] using hLb) hab (by
      intro x hxs hxt
      have hp : x.val ∉ ({pre.fst,pre.snd} : Set V) := by
        rintro (hh | hh)
        · exact hxs (Subtype.ext (hh.trans hes.symm))
        · exact hxt (Subtype.ext (hh.trans het.symm))
      simpa only [hce] using hboundsA x hp)
  obtain ⟨T,r,hT,hrs,hrt,hboundaryB⟩ := D.exposed_disk_boundary hD.simple hD.inner
  have hwA : w ∈ A := ((hinter w).mpr (Or.inr rfl)).1
  have hvA : outer.snd ∈ A := ((hinter outer.snd).mpr (Or.inl rfl)).1
  have hwv : G.Adj w outer.snd := by
    have hh := r.adj
    change G.Adj r.fst.val r.snd.val at hh
    simpa only [hrs,hrt] using hh
  let ca := cA ⟨w,hwA⟩
  let cb := cA ⟨outer.snd,hvA⟩
  let LB := chordLists L w outer.snd ca cb
  have hcolors : ca ≠ cb := cA.valid (show (G.induce A).Adj ⟨w,hwA⟩ ⟨outer.snd,hvA⟩ from hwv)
  have hprotected := (D.protected_vertices hD.simple pre.fst (ht ▸ pre.adj.symm)).2.2
  have hboundsB := R.induced_chord_list_bounds outer B T r hboundaryB L
    {pre.fst,pre.snd} w outer.snd ca cb (by
      intro x hx
      have hh := hprotected x.val x.property (by
        rcases hx with hx | hx
        · exact Or.inr hx
        · exact Or.inl (hx.trans ht))
      exact hh.symm)
    (fun x hx hp => (hbound x (fun h => hp (Or.inl h)) (fun h => hp (Or.inr h))).1
      (hprebound ▸ hx))
    (fun x hx hp => (hbound x (fun h => hp (Or.inl h)) (fun h => hp (Or.inr h))).2
      (fun hh => hx (hprebound.symm ▸ hh)))
  obtain ⟨cB,hcB⟩ := solve B hB T r hT (fun x => LB x.val) ca cb
    (by simp [LB,chordLists,hrs]) (by simp [LB,chordLists,hrt,hwv.ne.symm]) hcolors (by
      intro x hxs hxt
      exact hboundsB x (fun hh => hxs (Subtype.ext (hh.trans hrs.symm)))
        (fun hh => hxt (Subtype.ext (hh.trans hrt.symm))))
  obtain ⟨col,hcol,_,_⟩ := glue_along_chord G A B L w outer.snd hwA hvA hwv
    hcov hedges (fun x hx hy => ((hinter x).mp ⟨hx,hy⟩).symm) cA hcA cB hcB
  exact ⟨col,hcol⟩

end JSP512Probe.RotationSystem
