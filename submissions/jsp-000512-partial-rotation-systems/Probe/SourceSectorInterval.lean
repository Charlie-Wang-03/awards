import Probe.SectorFanRoute
import Probe.SplitFaceInterval
import Probe.OuterFaceFan

namespace JSP512Probe.RotationSystem
open CycleSurgery
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G) (v : V)

/-- Extract an actual inverse source-rotation interval of closed sectors,
stopping before the exceptional sector. -/
theorem source_sector_interval (root stop : G.Dart) (hr : root.fst = v)
    (hs : stop.fst = v) (hne : root ≠ stop)
    (hclose : ∀ d, d.fst = v → d ≠ stop → R.face (R.face (R.face d.symm)) = d.symm) :
    ∃ n : ℕ, ∃ d : Fin (n+1) → G.Dart,
      d 0 = root ∧ (∀ i, (d i).fst = v) ∧
      (∀ i, R.face (R.face (R.face (d i).symm)) = (d i).symm) ∧
      (∀ i : Fin n, R.rotate (d i.succ) = d i.castSucc) ∧
      Function.Injective d ∧ (∀ i, d i ≠ stop) ∧ R.rotate stop = d (Fin.last n) := by
  classical
  let r : {d : G.Dart // d.fst = v} := ⟨root, hr⟩
  let s : {d : G.Dart // d.fst = v} := ⟨stop, hs⟩
  let σ : Equiv.Perm {d : G.Dart // d.fst = v} := (R.sourceRotation v).symm
  have hne' : r ≠ s := fun hh => hne (congrArg Subtype.val hh)
  have hcycle : σ.SameCycle r s := by
    apply Equiv.Perm.SameCycle.inv
    apply (subtype_cycles R.rotate _ (fun d => by rw [R.source]) r s).mpr
    exact R.local_cycle root stop (hr.trans hs.symm)
  obtain ⟨m, hm, hstop, hinj, _, hmem⟩ := split_cycle_interval σ r s hne' hcycle
  have havoid : ∀ i : Fin m, ((σ ^ i.val) r).val ≠ stop := by
    intro i hh
    have he : (σ ^ i.val) r = s := Subtype.ext hh
    have hc := (hmem s).mpr ⟨i.val, i.isLt, he⟩
    exact swap_splits σ r s hne' hcycle hc
  cases m with
  | zero => omega
  | succ n =>
    let d := fun i : Fin (n+1) => ((σ ^ i.val) r).val
    refine ⟨n, d, rfl, fun i => ((σ ^ i.val) r).property,
      fun i => hclose (d i) ((σ ^ i.val) r).property (havoid i), ?_, ?_, havoid, ?_⟩
    · intro i
      have hh : (R.sourceRotation v) ((σ ^ i.succ.val) r) = (σ ^ i.castSucc.val) r := by
        rw [Fin.val_succ, pow_succ', Equiv.Perm.mul_apply]
        exact (R.sourceRotation v).apply_symm_apply _
      exact congrArg Subtype.val hh
    · intro i j hh
      exact hinj (Subtype.ext hh)
    · have hh : (R.sourceRotation v) s = (σ ^ n) r := by
        rw [← hstop, pow_succ', Equiv.Perm.mul_apply]
        exact (R.sourceRotation v).apply_symm_apply _
      exact congrArg Subtype.val hh

/-- At a simple disk boundary, the non-outer sectors provide an actual finite
restoration interval without assuming global triangularity. -/
theorem outer_source_sector_interval (outer : G.Dart)
    (hsimple : ∀ x y, R.face.SameCycle outer x → R.face.SameCycle outer y →
      x.fst = y.fst → x = y)
    (hinner : ∀ x, ¬R.face.SameCycle outer x → R.face (R.face (R.face x)) = x)
    (root : G.Dart) (hr : root.fst = outer.snd) (hne : root ≠ outer.symm) :
    ∃ n : ℕ, ∃ d : Fin (n+1) → G.Dart,
      d 0 = root ∧ (∀ i, (d i).fst = outer.snd) ∧
      (∀ i, R.face (R.face (R.face (d i).symm)) = (d i).symm) ∧
      (∀ i : Fin n, R.rotate (d i.succ) = d i.castSucc) ∧
      Function.Injective d ∧ (∀ i, d i ≠ outer.symm) ∧ R.rotate outer.symm = d (Fin.last n) := by
  exact R.source_sector_interval outer.snd root outer.symm hr rfl hne
    (fun d hd hn => R.outer_face_fan outer hsimple hinner d hd hn)

end JSP512Probe.RotationSystem
