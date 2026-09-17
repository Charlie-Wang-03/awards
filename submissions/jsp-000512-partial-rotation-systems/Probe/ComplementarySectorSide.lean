import Probe.SplitSideFullRoute
import Probe.ChordSectorRoute
import Probe.ComplementarySectorInterval

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

/-- A path terminating at the second cut belongs to the first split component:
the terminal facial step is redirected to the first cut. -/
theorem split_path_ending_at_cut (a b : G.Dart) (hab : a.fst = b.fst)
    (n : ℕ) (d : Fin (n+1) → G.Dart)
    (hstep : ∀ i : Fin n, R.face (d i.castSucc) = d i.succ)
    (ha : ∀ i : Fin n, d i.succ ≠ a) (hb : ∀ i : Fin n, d i.succ ≠ b)
    (hend : R.face (d (Fin.last n)) = b) :
    ∀ i, (RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)).Reachable
      (RefinedRotation.vertex G (R.splitRotation a b) (d i))
      (RefinedRotation.vertex G (R.splitRotation a b) a) := by
  let H := RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)
  let S := RefinedRotation.rotation G (R.splitRotation a b) (R.split_source a b hab)
  let E := RefinedRotation.dartEquiv G (R.splitRotation a b) (R.split_source a b hab)
  have ht : S.face (E (d (Fin.last n))) = E a := by
    rw [RefinedRotation.face_dart]
    change E (Equiv.swap a b (R.face (d (Fin.last n)))) = E a
    rw [hend, Equiv.swap_apply_right]
  have hv : (E (d (Fin.last n))).snd = (E a).fst := by
    rw [← ht, S.face_source]
  have hl := (E (d (Fin.last n))).adj.reachable
  rw [hv] at hl
  have hr := R.split_path_in_component a b hab (d 0) n d
    SimpleGraph.Reachable.rfl hstep ha hb
  exact fun i => (hr i).trans ((hr (Fin.last n)).symm.trans hl)

/-- The complementary triangular sectors lie in the old-boundary split
component. The last sector points to the exposed cut before splitting and
therefore to the old-boundary cut afterwards. -/
theorem complementary_sector_side (outer : G.Dart)
    (hsimple : ∀ x y, R.face.SameCycle outer x → R.face.SameCycle outer y →
      x.fst = y.fst → x = y)
    (x : (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hx : R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) x).val)
    (root : G.Dart) (hr : root.fst = outer.snd)
    (htr : R.face (R.face (R.face root.symm)) = root.symm)
    (n : ℕ) (d : Fin (n+1) → G.Dart)
    (hv : ∀ i, (d i).fst = outer.snd)
    (ht : ∀ i, R.face (R.face (R.face (d i).symm)) = (d i).symm)
    (ha : ∀ i, d i ≠ outer.symm) (hb : ∀ i, d i ≠ root)
    (hp : ∀ i : Fin n, R.rotate (d i.succ) = d i.castSucc)
    (hend : R.rotate root = d (Fin.last n)) :
    let S := R.deleteVertex outer.snd
    let y := R.sectorDeletedDart outer.snd root hr htr
    let f := fun i => R.sectorDeletedDart outer.snd (d i) (hv i) (ht i)
    ∀ hxy : x.fst = y.fst, ∀ i,
      (RefinedRotation.graph _ (S.splitRotation x y) (S.split_source x y hxy)).Reachable
        (RefinedRotation.vertex _ (S.splitRotation x y) (f i))
        (RefinedRotation.vertex _ (S.splitRotation x y) x) := by
  dsimp only
  intro hxy
  apply (R.deleteVertex outer.snd).split_path_ending_at_cut x _ hxy n
  · intro i
    exact R.sector_predecessor_step outer.snd _ _ _ _ (hp i) _ _
  · intro i hh
    exact R.deleted_sector_not_old_outer outer hsimple _ (hv i.succ) (ha i.succ)
      (ht i.succ) (hh.symm ▸ hx)
  · intro i hh
    exact hb i.succ (R.sector_target_injective outer.snd _ _ _ _ _ _
      (congrArg (fun z : (VertexDeletedGraph (G := G) outer.snd).Dart => z.snd) hh))
  · exact R.sector_predecessor_step outer.snd _ _ _ _ hend _ _

/-- The complementary interval yields a full initialized restoration route
on the actual old-boundary side, including its first sector. -/
theorem complementary_sector_full_side_route (outer : G.Dart)
    (hsimple : ∀ x y, R.face.SameCycle outer x → R.face.SameCycle outer y →
      x.fst = y.fst → x = y)
    (x : (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hx : R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) x).val)
    (root : G.Dart) (hr : root.fst = outer.snd)
    (htr : R.face (R.face (R.face root.symm)) = root.symm)
    (n : ℕ) (d : Fin (n+1) → G.Dart)
    (hv : ∀ i, (d i).fst = outer.snd)
    (ht : ∀ i, R.face (R.face (R.face (d i).symm)) = (d i).symm)
    (ha : ∀ i, d i ≠ outer.symm) (hb : ∀ i, d i ≠ root)
    (hp : ∀ i : Fin n, R.rotate (d i.succ) = d i.castSucc)
    (hinj : Function.Injective d) (hend : R.rotate root = d (Fin.last n)) :
    let H := VertexDeletedGraph (G := G) outer.snd
    let S := R.deleteVertex outer.snd
    let y := R.sectorDeletedDart outer.snd root hr htr
    let f := fun i => R.sectorDeletedDart outer.snd (d i) (hv i) (ht i)
    ∀ (hxy : x.fst = y.fst) (hne : x ≠ y) (hc : H.Preconnected)
      (hz : S.HasGenusZero) (hf : S.face.SameCycle x y),
      letI : Fintype (S.splitSide x y hxy x) := Fintype.ofFinite _
      let hreach := R.complementary_sector_side outer hsimple x hx root hr htr
        n d hv ht ha hb hp hend hxy
      let g := fun i => S.splitSideDart x y hxy x (f i) (hreach i)
      let K := H.induce (S.splitSide x y hxy x)
      let T := S.splitSideRotation x y hxy hne hc hz hf x
      let a := (T.face.symm (g 0)).symm
      EdgeInsertion.FanRoute (fanStartGraph K a) (startFan K T a)
        (startAnchor K a)
        ((List.ofFn g).map (startOldDart K a)) := by
  classical
  dsimp only
  intro hxy hne hc hz hf
  let y := R.sectorDeletedDart outer.snd root hr htr
  let S := R.deleteVertex outer.snd
  let f := fun i => R.sectorDeletedDart outer.snd (d i) (hv i) (ht i)
  let : Fintype (S.splitSide x y hxy x) := Fintype.ofFinite _
  have hreach := R.complementary_sector_side outer hsimple x hx root hr htr
    n d hv ht ha hb hp hend hxy
  apply (R.deleteVertex outer.snd).splitSideDart_full_start_route x y hxy
    hne hc hz hf x n f (hreach 0)
  · intro i
    exact R.sector_predecessor_step outer.snd _ _ _ _ (hp i) _ _
  · intro i hh
    change R.sectorDeletedDart outer.snd (d i.succ) (hv i.succ) (ht i.succ) = x at hh
    exact R.deleted_sector_not_old_outer outer hsimple _ (hv i.succ) (ha i.succ)
      (ht i.succ) (hh.symm ▸ hx)
  · intro i hh
    exact hb i.succ (R.sector_target_injective outer.snd _ _ _ _ _ _
      (congrArg (fun z : (VertexDeletedGraph (G := G) outer.snd).Dart => z.snd) hh))
  · intro i j hh
    exact hinj (R.sector_target_injective outer.snd _ _ _ _ _ _ hh)
  · exact R.sector_interval_source_avoidance outer.snd n d hv ht hp hinj root hend (hb 0).symm

end JSP512Probe.RotationSystem
