import Probe.SourceNeighborPartition

namespace JSP512Probe.RotationSystem
open CycleSurgery
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G) (v : V)

/-- The complementary interval omits the exceptional sector at its start and
the first interval's start at its end. A genuine chord makes it nonempty. -/
theorem complementary_sector_interval (root stop : G.Dart) (hr : root.fst = v)
    (hs : stop.fst = v) (hne : root ≠ stop) (hchord : R.rotate root ≠ stop)
    (hclose : ∀ d, d.fst = v → d ≠ stop → R.face (R.face (R.face d.symm)) = d.symm) :
    ∃ n : ℕ, ∃ d : Fin (n+1) → G.Dart,
      R.rotate (d 0) = stop ∧ (∀ i, (d i).fst = v) ∧
      (∀ i, R.face (R.face (R.face (d i).symm)) = (d i).symm) ∧
      (∀ i : Fin n, R.rotate (d i.succ) = d i.castSucc) ∧
      Function.Injective d ∧ (∀ i, d i ≠ stop ∧ d i ≠ root) ∧
      R.rotate root = d (Fin.last n) := by
  classical
  let r : {d : G.Dart // d.fst = v} := ⟨root,hr⟩
  let s : {d : G.Dart // d.fst = v} := ⟨stop,hs⟩
  let σ : Equiv.Perm {d : G.Dart // d.fst = v} := (R.sourceRotation v).symm
  have hne' : s ≠ r := fun hh => hne (congrArg Subtype.val hh).symm
  have hc : σ.SameCycle s r := by
    apply Equiv.Perm.SameCycle.inv
    apply (subtype_cycles R.rotate _ (fun d => by rw [R.source]) s r).mpr
    exact R.local_cycle stop root (hs.trans hr.symm)
  obtain ⟨m, hm, hmr, hinj, _, hmem⟩ := split_cycle_interval σ s r hne' hc
  have hm2 : 2 ≤ m := by
    by_contra hh
    have he : m = 1 := by omega
    subst m
    have he : σ s = r := by simpa using hmr
    have ht := congrArg (R.sourceRotation v) he
    have hs' : (R.sourceRotation v) r = s := by
      rw [(R.sourceRotation v).apply_symm_apply] at ht
      exact ht.symm
    exact hchord (congrArg Subtype.val hs')
  obtain ⟨n, hmn⟩ : ∃ n, m = n+2 := ⟨m-2,by omega⟩
  subst m
  let d := fun i : Fin (n+1) => ((σ ^ (i.val+1)) s).val
  have hstop : ∀ i : Fin (n+1), d i ≠ stop := by
    intro i hh
    have hEq : (σ ^ (i.val+1)) s = (σ ^ 0) s := Subtype.ext hh
    have hidx := hinj (a₁ := ⟨i.val+1,by omega⟩) (a₂ := ⟨0,by omega⟩) hEq
    have hv := congrArg Fin.val hidx
    simp at hv
  have hroot : ∀ i : Fin (n+1), d i ≠ root := by
    intro i hh
    have hEq : (σ ^ (i.val+1)) s = r := Subtype.ext hh
    have hsr := (hmem r).mpr ⟨i.val+1,by omega,hEq⟩
    exact swap_splits σ s r hne' hc hsr
  refine ⟨n,d,?_,fun i => ((σ ^ (i.val+1)) s).property,
    fun i => hclose _ ((σ ^ (i.val+1)) s).property (hstop i),?_,?_,
    fun i => ⟨hstop i,hroot i⟩,?_⟩
  · exact congrArg Subtype.val ((R.sourceRotation v).apply_symm_apply s)
  · intro i
    have hh : (R.sourceRotation v) ((σ ^ (i.succ.val+1)) s) =
        (σ ^ (i.castSucc.val+1)) s := by
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact (R.sourceRotation v).apply_symm_apply _
    exact congrArg Subtype.val hh
  · intro i j hh
    have hidx := hinj (a₁ := ⟨i.val+1,by omega⟩) (a₂ := ⟨j.val+1,by omega⟩) (Subtype.ext hh)
    apply Fin.ext
    have hv := congrArg Fin.val hidx
    simpa using hv
  · have hh : (R.sourceRotation v) r = (σ ^ (n+1)) s := by
      rw [← hmr, show n+2 = (n+1)+1 by omega, pow_succ', Equiv.Perm.mul_apply]
      exact (R.sourceRotation v).apply_symm_apply _
    exact congrArg Subtype.val hh

/-- A genuine boundary chord supplies the nonempty complementary closed-sector
interval. Its first sector begins at the old left boundary neighbor and its
last target is the surviving chord endpoint. -/
theorem outer_complementary_sector_interval (outer : G.Dart)
    (hsimple : ∀ x y, R.face.SameCycle outer x → R.face.SameCycle outer y →
      x.fst = y.fst → x = y)
    (hinner : ∀ x, ¬R.face.SameCycle outer x → R.face (R.face (R.face x)) = x)
    (e : G.Dart) (he : e.fst = outer.snd)
    (hleft : e.snd ≠ outer.fst) (hright : e.snd ≠ (R.face outer).snd) :
    ∃ n : ℕ, ∃ d : Fin (n+1) → G.Dart,
      R.rotate (d 0) = outer.symm ∧ (∀ i, (d i).fst = outer.snd) ∧
      (∀ i, R.face (R.face (R.face (d i).symm)) = (d i).symm) ∧
      (∀ i : Fin n, R.rotate (d i.succ) = d i.castSucc) ∧
      Function.Injective d ∧
      (∀ i, d i ≠ outer.symm ∧ d i ≠ R.rotate.symm e) ∧
      e = d (Fin.last n) := by
  have hr : (R.rotate.symm e).fst = outer.snd := by
    have hh := R.source (R.rotate.symm e)
    rw [R.rotate.apply_symm_apply] at hh
    exact hh.symm.trans he
  have hn : R.rotate.symm e ≠ outer.symm := by
    intro hh
    have ht := congrArg R.rotate hh
    rw [R.rotate.apply_symm_apply] at ht
    exact hright (congrArg (fun x : G.Dart => x.snd) ht)
  have hc : R.rotate (R.rotate.symm e) ≠ outer.symm := by
    rw [R.rotate.apply_symm_apply]
    intro hh
    exact hleft (congrArg (fun x : G.Dart => x.snd) hh)
  obtain ⟨n,d,h0,hd,ht,hstep,hi,ha,hlast⟩ :=
    R.complementary_sector_interval outer.snd (R.rotate.symm e) outer.symm hr rfl hn hc
      (fun x hx hn => R.outer_face_fan outer hsimple hinner x hx hn)
  rw [R.rotate.apply_symm_apply] at hlast
  exact ⟨n,d,h0,hd,ht,hstep,hi,ha,hlast⟩

end JSP512Probe.RotationSystem
