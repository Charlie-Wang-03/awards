import Probe.SourceSectorInterval
import Probe.SplitSideFullRoute

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A nonrepeating inverse-rotation interval ending just before a distinct
stop cannot contain the predecessor of its starting point. -/
theorem sector_interval_avoids_predecessor (n : ℕ) (d : Fin (n+1) → G.Dart)
    (hp : ∀ i : Fin n, R.rotate (d i.succ) = d i.castSucc)
    (hinj : Function.Injective d) (stop : G.Dart)
    (hlast : R.rotate stop = d (Fin.last n)) (hstop : stop ≠ d 0) :
    ∀ i, d i ≠ R.rotate (d 0) := by
  intro i he
  by_cases hi : i.val < n
  · let j : Fin n := ⟨i.val, hi⟩
    have hj : j.castSucc = i := Fin.ext rfl
    have hh : R.rotate (d j.succ) = R.rotate (d 0) := by
      rw [hp, hj, he]
    have hz := hinj (R.rotate.injective hh)
    have hv := congrArg Fin.val hz
    simp at hv
  · have hj : i = Fin.last n := Fin.ext (by simp; omega)
    rw [hj, ← hlast] at he
    exact hstop (R.rotate.injective he)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- All targets of a complete sector interval avoid its initial source,
including the first target. This keeps the chord-endpoint attachment distinct. -/
theorem sector_interval_source_avoidance (v : V) (n : ℕ) (d : Fin (n+1) → G.Dart)
    (hv : ∀ i, (d i).fst = v)
    (ht : ∀ i, R.face (R.face (R.face (d i).symm)) = (d i).symm)
    (hp : ∀ i : Fin n, R.rotate (d i.succ) = d i.castSucc)
    (hinj : Function.Injective d) (stop : G.Dart)
    (hlast : R.rotate stop = d (Fin.last n)) (hstop : stop ≠ d 0) :
    let f := fun i => R.sectorDeletedDart v (d i) (hv i) (ht i)
    ∀ i, (f i).snd ≠ (f 0).fst := by
  dsimp only
  intro i he
  have hh := congrArg Subtype.val he
  change (R.face (R.rotate (d i))).snd = (R.face (R.rotate (d 0))).fst at hh
  rw [(R.sector_endpoints_of_closed (d i) (ht i)).2,
    (R.sector_endpoints_of_closed (d 0) (ht 0)).1] at hh
  have hd : d i = R.rotate (d 0) := SimpleGraph.Dart.ext _ _
    (Prod.ext ((hv i).trans ((hv 0).symm.trans (R.source (d 0)).symm)) hh)
  exact R.sector_interval_avoids_predecessor n d hp hinj stop hlast hstop i hd

end JSP512Probe.RotationSystem
