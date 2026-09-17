import Probe.FanStartRoute
import Probe.FanSplicing
import Mathlib.Data.List.OfFn

namespace JSP512Probe.EdgeInsertion
/-- A finite sequence of verified successor steps gives a facial route. -/
theorem FaceRoute.of_steps {α : Type*} (f : α → α) (n : ℕ)
    (d : Fin (n+1) → α) (hs : ∀ i : Fin n, f (d i.castSucc) = d i.succ) :
    FaceRoute f (d 0) (List.ofFn (fun i : Fin n => d i.succ)) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    rw [List.ofFn_succ]
    exact ⟨hs 0, ih (fun i => d i.succ) (fun i => hs i.succ)⟩
end JSP512Probe.EdgeInsertion

namespace JSP512Probe.RotationSystem
open EdgeInsertion
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G) (v : V)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Targets of closed sector sides identify their original outgoing darts.
Only these sectors need to be triangular, not the entire graph. -/
theorem sector_target_injective (d e : G.Dart) (hd : d.fst = v) (he : e.fst = v)
    (htd : R.face (R.face (R.face d.symm)) = d.symm)
    (hte : R.face (R.face (R.face e.symm)) = e.symm)
    (h : (R.sectorDeletedDart v d hd htd).snd = (R.sectorDeletedDart v e he hte).snd) : d = e := by
  have hh := congrArg Subtype.val h
  change (R.face (R.rotate d)).snd = (R.face (R.rotate e)).snd at hh
  rw [(R.sector_endpoints_of_closed d htd).2, (R.sector_endpoints_of_closed e hte).2] at hh
  exact SimpleGraph.Dart.ext _ _ (Prod.ext (hd.trans he.symm) hh)

/-- A consecutive inverse-rotation interval of closed sectors becomes an
actual route on the vertex-deleted graph. -/
theorem sector_interval_route (n : ℕ) (d : Fin (n+1) → G.Dart)
    (hv : ∀ i, (d i).fst = v)
    (ht : ∀ i, R.face (R.face (R.face (d i).symm)) = (d i).symm)
    (hp : ∀ i : Fin n, R.rotate (d i.succ) = d i.castSucc) :
    let f := fun i => R.sectorDeletedDart v (d i) (hv i) (ht i)
    FaceRoute (R.deleteVertex v).face (f 0) (List.ofFn (fun i : Fin n => f i.succ)) := by
  dsimp only
  apply FaceRoute.of_steps (R.deleteVertex v).face n
    (fun i => R.sectorDeletedDart v (d i) (hv i) (ht i))
  intro i
  exact R.sector_predecessor_step v (d i.castSucc) (d i.succ)
    (hv i.castSucc) (hv i.succ) (hp i) (ht i.castSucc) (ht i.succ)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Distinct source darts give pairwise distinct target vertices along the
surviving sector path, the stronger condition needed for fan restoration. -/
theorem sector_interval_targets (n : ℕ) (d : Fin (n+1) → G.Dart)
    (hv : ∀ i, (d i).fst = v)
    (ht : ∀ i, R.face (R.face (R.face (d i).symm)) = (d i).symm)
    (hinj : Function.Injective d) :
    let f := fun i => R.sectorDeletedDart v (d i) (hv i) (ht i)
    (List.ofFn (fun i : Fin n => f i.succ)).Pairwise (fun x y => x.snd ≠ y.snd) ∧
      ∀ x ∈ List.ofFn (fun i : Fin n => f i.succ), x.snd ≠ (f 0).snd := by
  dsimp only
  constructor
  · apply List.pairwise_ofFn.mpr
    intro i j hij he
    have hd := hinj (R.sector_target_injective v _ _ _ _ _ _ he)
    have hh : i = j := by simpa using hd
    exact (ne_of_lt hij) hh
  · intro x hx he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    have hd := hinj (R.sector_target_injective v _ _ _ _ _ _ he)
    have hh := congrArg Fin.val hd
    simp at hh

/-- Closed-sector intervals already supply all route/target conditions for
fresh-center fan restoration on the actual deleted graph. -/
theorem sector_interval_start_route (n : ℕ) (d : Fin (n+1) → G.Dart)
    (hv : ∀ i, (d i).fst = v)
    (ht : ∀ i, R.face (R.face (R.face (d i).symm)) = (d i).symm)
    (hp : ∀ i : Fin n, R.rotate (d i.succ) = d i.castSucc)
    (hinj : Function.Injective d) :
    let H := VertexDeletedGraph (G := G) v
    let S := R.deleteVertex v
    let f := fun i => R.sectorDeletedDart v (d i) (hv i) (ht i)
    let a := (f 0).symm
    let ds := List.ofFn (fun i : Fin n => f i.succ)
    FanRoute (fanStartGraph H a) (startFan H S a) (startAnchor H a)
      (ds.map (startOldDart H a)) := by
  classical
  dsimp only
  obtain ⟨hpair, havoid⟩ := R.sector_interval_targets v n d hv ht hinj
  apply startFan_route
  · exact R.sector_interval_route v n d hv ht hp
  · exact hpair
  · exact havoid

end JSP512Probe.RotationSystem
