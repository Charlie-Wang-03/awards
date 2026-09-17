import Probe.SplitSideDarts
import Probe.SourceSectorInterval
import Probe.SectorEndpointAvoidance

namespace JSP512Probe.RotationSystem
open EdgeInsertion
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every nonexceptional sector at the deleted outer vertex is disjoint from
the original outer face, even if its vertices also lie on that boundary. -/
theorem deleted_sector_not_old_outer (outer : G.Dart)
    (hsimple : ∀ x y, R.face.SameCycle outer x → R.face.SameCycle outer y →
      x.fst = y.fst → x = y)
    (d : G.Dart) (hd : d.fst = outer.snd) (hne : d ≠ outer.symm)
    (ht : R.face (R.face (R.face d.symm)) = d.symm) :
    ¬R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd)
      (R.sectorDeletedDart outer.snd d hd ht)).val := by
  apply R.inner_sector_not_outer outer d
  intro hh
  have he := R.face.injective (hsimple (R.face d.symm) (R.face outer) hh.apply_right
    Equiv.Perm.SameCycle.rfl.apply_right (by rw [R.face_source, R.face_source]; exact hd))
  apply hne
  simpa only [SimpleGraph.Dart.symm_symm] using congrArg SimpleGraph.Dart.symm he

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A sector interval starting at the exposed chord occurrence avoids the
old-boundary cut everywhere and the exposed-sector cut after its first dart. -/
theorem chord_sector_cut_avoidance (outer : G.Dart)
    (hsimple : ∀ x y, R.face.SameCycle outer x → R.face.SameCycle outer y →
      x.fst = y.fst → x = y)
    (x : (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hx : R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) x).val)
    (n : ℕ) (d : Fin (n+1) → G.Dart)
    (hv : ∀ i, (d i).fst = outer.snd)
    (ht : ∀ i, R.face (R.face (R.face (d i).symm)) = (d i).symm)
    (he : ∀ i, d i ≠ outer.symm) (hinj : Function.Injective d) :
    let f := fun i => R.sectorDeletedDart outer.snd (d i) (hv i) (ht i)
    (∀ i, f i ≠ x) ∧ ∀ i : Fin n, f i.succ ≠ f 0 := by
  dsimp only
  constructor
  · intro i hh
    have hn := R.deleted_sector_not_old_outer outer hsimple (d i) (hv i) (he i) (ht i)
    exact hn (hh.symm ▸ hx)
  · intro i hh
    have hd := R.sector_target_injective outer.snd _ _ _ _ _ _
      (congrArg (fun e : (VertexDeletedGraph (G := G) outer.snd).Dart => e.snd) hh)
    have hi := congrArg Fin.val (hinj hd)
    simp at hi

/-- The complete sector interval beginning at the exposed chord occurrence
provides an initialized fan route on its actual induced split side. -/
theorem chord_sector_side_route (outer : G.Dart)
    (hsimple : ∀ x y, R.face.SameCycle outer x → R.face.SameCycle outer y →
      x.fst = y.fst → x = y)
    (x : (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hx : R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) x).val)
    (n : ℕ) (d : Fin (n+1) → G.Dart)
    (hv : ∀ i, (d i).fst = outer.snd)
    (ht : ∀ i, R.face (R.face (R.face (d i).symm)) = (d i).symm)
    (he : ∀ i, d i ≠ outer.symm) (hinj : Function.Injective d)
    (hp : ∀ i : Fin n, R.rotate (d i.succ) = d i.castSucc) :
    let H := VertexDeletedGraph (G := G) outer.snd
    let S := R.deleteVertex outer.snd
    let f := fun i => R.sectorDeletedDart outer.snd (d i) (hv i) (ht i)
    ∀ (hxy : x.fst = (f 0).fst) (hc : H.Preconnected) (hz : S.HasGenusZero)
      (hf : S.face.SameCycle x (f 0)),
      let hne := (R.chord_sector_cut_avoidance outer hsimple x hx n d hv ht he hinj).1 0
      letI : Fintype (S.splitSide x (f 0) hxy (f 0)) := Fintype.ofFinite _
      let hreach := S.split_path_in_component x (f 0) hxy (f 0) n f
        SimpleGraph.Reachable.rfl
        (fun i => R.sector_predecessor_step outer.snd _ _ _ _ (hp i) _ _)
        (fun i => (R.chord_sector_cut_avoidance outer hsimple x hx n d hv ht he hinj).1 i.succ)
        (R.chord_sector_cut_avoidance outer hsimple x hx n d hv ht he hinj).2
      let g := fun i => S.splitSideDart x (f 0) hxy (f 0) (f i) (hreach i)
      let K := H.induce (S.splitSide x (f 0) hxy (f 0))
      let T := S.splitSideRotation x (f 0) hxy hne.symm hc hz hf (f 0)
      let a := (g 0).symm
      FanRoute (fanStartGraph K a) (startFan K T a) (startAnchor K a)
        ((List.ofFn (fun i : Fin n => g i.succ)).map (startOldDart K a)) := by
  classical
  dsimp only
  intro hxy hc hz hf
  let f := fun i => R.sectorDeletedDart outer.snd (d i) (hv i) (ht i)
  have hcuts := R.chord_sector_cut_avoidance outer hsimple x hx n d hv ht he hinj
  have htarget : Function.Injective (fun i => (f i).snd) := by
    intro i j hij
    apply hinj
    exact R.sector_target_injective outer.snd _ _ _ _ _ _ hij
  exact (R.deleteVertex outer.snd).splitSideDart_start_route x (f 0) hxy
    (hcuts.1 0).symm hc hz hf (f 0) n f SimpleGraph.Reachable.rfl
    (fun i => R.sector_predecessor_step outer.snd _ _ _ _ (hp i) _ _)
    (fun i => hcuts.1 i.succ) hcuts.2 htarget

/-- The actual exposed chord-side interval, including its first sector and
chord-endpoint attachment, supplies a complete initialized fan route. -/
theorem chord_sector_full_side_route (outer : G.Dart)
    (hsimple : ∀ x y, R.face.SameCycle outer x → R.face.SameCycle outer y →
      x.fst = y.fst → x = y)
    (x : (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hx : R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) x).val)
    (n : ℕ) (d : Fin (n+1) → G.Dart)
    (hv : ∀ i, (d i).fst = outer.snd)
    (ht : ∀ i, R.face (R.face (R.face (d i).symm)) = (d i).symm)
    (he : ∀ i, d i ≠ outer.symm) (hinj : Function.Injective d)
    (hp : ∀ i : Fin n, R.rotate (d i.succ) = d i.castSucc)
    (stop : G.Dart) (hlast : R.rotate stop = d (Fin.last n)) (hstop : stop ≠ d 0) :
    let H := VertexDeletedGraph (G := G) outer.snd
    let S := R.deleteVertex outer.snd
    let f := fun i => R.sectorDeletedDart outer.snd (d i) (hv i) (ht i)
    ∀ (hxy : x.fst = (f 0).fst) (hc : H.Preconnected) (hz : S.HasGenusZero)
      (hf : S.face.SameCycle x (f 0)),
      let hne := (R.chord_sector_cut_avoidance outer hsimple x hx n d hv ht he hinj).1 0
      letI : Fintype (S.splitSide x (f 0) hxy (f 0)) := Fintype.ofFinite _
      let hreach := S.split_path_in_component x (f 0) hxy (f 0) n f
        SimpleGraph.Reachable.rfl
        (fun i => R.sector_predecessor_step outer.snd _ _ _ _ (hp i) _ _)
        (fun i => (R.chord_sector_cut_avoidance outer hsimple x hx n d hv ht he hinj).1 i.succ)
        (R.chord_sector_cut_avoidance outer hsimple x hx n d hv ht he hinj).2
      let g := fun i => S.splitSideDart x (f 0) hxy (f 0) (f i) (hreach i)
      let K := H.induce (S.splitSide x (f 0) hxy (f 0))
      let T := S.splitSideRotation x (f 0) hxy hne.symm hc hz hf (f 0)
      let a := (T.face.symm (g 0)).symm
      FanRoute (fanStartGraph K a) (startFan K T a) (startAnchor K a)
        ((List.ofFn g).map (startOldDart K a)) := by
  classical
  dsimp only
  intro hxy hc hz hf
  let f := fun i => R.sectorDeletedDart outer.snd (d i) (hv i) (ht i)
  have hcuts := R.chord_sector_cut_avoidance outer hsimple x hx n d hv ht he hinj
  have htarget : Function.Injective (fun i => (f i).snd) := by
    intro i j hij
    apply hinj
    exact R.sector_target_injective outer.snd _ _ _ _ _ _ hij
  exact (R.deleteVertex outer.snd).splitSideDart_full_start_route x (f 0) hxy
    (hcuts.1 0).symm hc hz hf (f 0) n f SimpleGraph.Reachable.rfl
    (fun i => R.sector_predecessor_step outer.snd _ _ _ _ (hp i) _ _)
    (fun i => hcuts.1 i.succ) hcuts.2 htarget
    (R.sector_interval_source_avoidance outer.snd n d hv ht hp hinj stop hlast hstop)

end JSP512Probe.RotationSystem
