import Probe.FiniteFan
import Probe.EarOuterBoundary

namespace JSP512Probe.EdgeInsertion
open RotationSystem CycleSurgery
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (R : RotationSystem G)

/-- Source simplicity is only needed on the old boundary occurrences that
will survive the fan. The route's darts are allowed to duplicate sources. -/
def ResidualBoundarySimple (a : G.Dart) (ds : List G.Dart) : Prop :=
  ∀ x y, R.face.SameCycle a.symm x → R.face.SameCycle a.symm y →
    x ∉ ds → y ∉ ds → x.fst = y.fst → x = y

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A route of missing spokes cannot contain the already present first spoke. -/
theorem FanRoute.first_spoke_not_mem (a : G.Dart) (ds : List G.Dart)
    (hr : FanRoute G R a ds) : R.rotate a ∉ ds := by
  intro hm
  have hmissing := (hr.missing (R.rotate a) hm).2
  apply hmissing
  have hadj := (R.rotate a).adj
  rwa [R.source] at hadj

/-- Simplicity of the eventual retained boundary propagates through an ear
insertion, even when the current entire outer face is not simple. -/
theorem FanRoute.residual_simple_tail (a d : G.Dart) (ds : List G.Dart)
    (hr : FanRoute G R a (d :: ds)) (hs : ResidualBoundarySimple G R a (d :: ds)) :
    let hn := (hr.missing d (by simp)).1
    let hm := (hr.missing d (by simp)).2
    let S := addEdge G R a d.symm hn hm
    let E := dartEquiv G a.fst d.snd hn hm
    ResidualBoundarySimple (addedGraph G a.fst d.snd hn) S (E (some (some a)))
      (ds.map (fun e => E (some (some e)))) := by
  classical
  dsimp only
  let hn := (hr.missing d (by simp)).1
  let hm := (hr.missing d (by simp)).2
  let S := addEdge G R a d.symm hn hm
  let E := dartEquiv G a.fst d.snd hn hm
  let f := fun e : G.Dart => E (some (some e))
  intro x y hx hy hnx hny hxy
  obtain ⟨u, hu, hud, hxu, hux⟩ :=
    added_outer_representative G R a d.symm hn hm hr.route.1 x hx
  obtain ⟨v, hv, hvd, hyv, hvy⟩ :=
    added_outer_representative G R a d.symm hn hm hr.route.1 y hy
  have survivor : ∀ (z : (addedGraph G a.fst d.snd hn).Dart) (w : G.Dart),
      w ≠ d → z ∉ ds.map f →
      z = (if w = R.rotate a then E (some none) else f w) → w ∉ d :: ds := by
    intro z w hwd hzn hzw hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hwd rfl
    · by_cases he : w = R.rotate a
      · subst w
        exact hr.first_spoke_not_mem G R a (d :: ds) (by simp [hw])
      · apply hzn
        rw [hzw, ite_eq_right he]
        exact List.mem_map.mpr ⟨w, hw, rfl⟩
  have huN := survivor x u hud hnx hux
  have hvN := survivor y v hvd hny hvy
  have huv := hs u v hu hv huN hvN (hxu.symm.trans (hxy.trans hyv))
  subst v
  exact hux.trans hvy.symm

end JSP512Probe.EdgeInsertion
